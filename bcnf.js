"use strict";
function elem(it, eType, appendToLast = false) {
    const element = document.createElement(eType);
    if (appendToLast)
        it[it.length - 1].appendChild(element);
    return element;
}
function newLi(it, str, addToList = false) {
    const listItem = elem(it, 'li', true);
    listItem.innerHTML = str;
    if (addToList)
        it.push(listItem);
}
Set.prototype.powerset = function (proper = false) {
    const array_set = Array.from(this);
    const final = new Array();
    const nonempty = true;
    const [i_start, i_end] = [nonempty ? 1 : 0, 2 ** this.size - (proper ? 1 : 0)];
    for (let i = i_start; i < i_end; i++) {
        const subset = new Set();
        for (let x = 0; x < this.size; x++) {
            if ((i >> x) & 1)
                subset.add(array_set[x]);
        }
        final.push(subset);
    }
    return final.toSorted((a, b) => a.size - b.size);
};
Set.prototype.equalTo = function (that) {
    if (this.size !== that.size)
        return false;
    for (const element of this.keys()) {
        if (!that.has(element))
            return false;
    }
    return true;
};
Set.prototype.diff = function (that) {
    let diff = new Set();
    for (const e of this.keys()) {
        if (!that.has(e))
            diff.add(e);
    }
    return diff;
};
Set.prototype.union = function (that) {
    return new Set([...this, ...that]);
};
Set.prototype.isSupersetOf = function (that) {
    for (const elem of that.keys()) {
        if (!this.has(elem))
            return false;
    }
    return true;
};
// ? FUNCTIONAL DEPENDENCIES ---------------------------------------
function splitFDs(fds) {
    return fds.flatMap(({ dets, deps }) => {
        return [...deps].map((dep) => ({ dets, deps: new Set([dep]) }));
    });
}
function combineFDs(fds) {
    let seenIndices = new Set();
    let newFDs = [];
    for (let i = 0; i < fds.length; i++) {
        if (seenIndices.has(i))
            continue;
        let deps = new Set(fds[i].deps);
        for (let j = i + 1; j < fds.length; j++) {
            if (fds[i].dets.equalTo(fds[j].dets)) {
                deps = deps.union(fds[j].deps);
                seenIndices.add(j);
            }
        }
        newFDs.push({ deps, dets: fds[i].dets });
    }
    return newFDs;
}
function closure(attribs, fds) {
    let [cAttribs, prevSize] = [new Set(attribs), -1];
    fds = splitFDs(fds);
    while (cAttribs.size != prevSize) {
        prevSize = cAttribs.size;
        for (const subset of cAttribs.powerset(false)) {
            for (const { dets, deps } of fds) {
                if (subset.equalTo(dets) && [...deps].some((dep) => !cAttribs.has(dep))) {
                    cAttribs = cAttribs.union(deps);
                }
            }
        }
    }
    return cAttribs;
}
function minimalBasis(fds) {
    let newFDs = [];
    for (const { dets: As, deps: Bs, dependantsExtra: Cs } of fds) {
        let flag = false;
        for (const subset of As.powerset(true)) {
            for (const { dets: Xs, deps: Ys } of newFDs) {
                flag = flag || (!Xs.equalTo(As) && Xs.equalTo(subset) && Ys.isSupersetOf(Bs));
            }
        }
        newFDs.push({
            dets: As, deps: Bs,
            dependantsExtra: Cs,
            minimal: !flag
        });
    }
    return newFDs;
}
function projectFDs(R) {
    let T = R.attributes.powerset(true).map((dets) => {
        const dependantsExtra = [];
        const deps = new Set();
        for (const attr of closure(dets, R.fds)) {
            if (R.attributes.has(attr) && !dets.has(attr)) {
                deps.add(attr);
            }
            dependantsExtra.push({
                isInAttributes: R.attributes.has(attr),
                isNotInSubset: !dets.has(attr),
                dep: attr,
            });
        }
        return {
            dets, deps,
            dependantsExtra, minimal: true
        };
    });
    return minimalBasis(T);
}
function bcnfCheck(it, { name, attributes, fds }) {
    const minimisedFDs = combineFDs(fds);
    if (minimisedFDs.length == 0)
        newLi(it, ` ✔ no FDs`);
    for (const { dets } of minimisedFDs) {
        let clos = closure(dets, fds);
        if (!clos.equalTo(attributes)) {
            newLi(it, ` ✘ ${closureStr(dets, clos)}`);
            return {
                dets,
                rel1: {
                    name: name + '1', fds,
                    attributes: clos,
                },
                rel2: {
                    name: name + '2', fds,
                    attributes: dets.union(attributes.diff(clos)),
                }
            };
        }
        newLi(it, ` ✔ ${closureStr(dets, clos)}`);
    }
    return undefined;
}
function checkRelation(R) {
    for (const { dets, deps } of R.fds) {
        for (const d in dets.union(deps).keys()) {
            if (!R.attributes.has(d))
                return false;
        }
    }
    return true;
}
// ? STRINGS -------------------------------------------------------
function closureStr(dets, closure) {
    let detsStr = `{${attribStr(dets)}}<sup>+</sup>`;
    if (closure !== undefined)
        detsStr += ` = {${attribStr(closure)}}`;
    return detsStr;
}
function relationStr(R) {
    return `${R.name}(${attribStr(R.attributes)})`;
}
function attribStr(attribs) {
    return Array.from(attribs).toSorted().join(', ');
}
function fdStr(fd) {
    return Array.from(fd.dets).toSorted().join('') + ' -> ' + Array.from(fd.deps).toSorted().join('');
}
function fdsStr(fds) {
    if (fds.length == 0)
        return 'none';
    return fds.map(fdStr).join(', ');
}
// ? PRINTING ------------------------------------------------------
function printRelation(it, R) {
    const relationContainer = elem(it, 'li', true);
    const containerForSteps = elem(it, 'ol');
    relationContainer.classList.add('relation-title');
    relationContainer.innerHTML = `
        <div><span>Relation</span> ${relationStr(R)}</div>
        <div><span>Functional Dependencies</span> {${fdsStr(combineFDs(R.fds))}}</div>
    `;
    relationContainer.appendChild(containerForSteps);
    it.push(containerForSteps);
}
function printFDs(it, fds) {
    const ul = elem(it, 'ul', true);
    it.push(ul);
    if (fds.length == 0)
        newLi(it, 'no FDs');
    for (const { dets, deps, minimal, dependantsExtra } of fds) {
        const closureWithDetails = dependantsExtra.toSorted((a, b) => a.dep.localeCompare(b.dep)).map(({ dep, isInAttributes, isNotInSubset }) => {
            if (!isInAttributes)
                return `<s>${dep}</s><sup>a</sup>`;
            if (!isNotInSubset)
                return `<s>${dep}</s><sup>b</sup>`;
            return dep;
        }).join(', ');
        let closure = closureStr(dets) + ` = {${closureWithDetails}}`;
        if (deps.size > 0) {
            let fdString = fdStr({ dets, deps });
            fdString = minimal ? fdString : `<s>${fdString}</s>`;
            closure = `${closure} // ${fdString}`;
        }
        newLi(it, closure);
    }
    it.pop();
}
function newSection(it, text, content, noIndent = false) {
    const header = elem(it, 'li');
    header.innerHTML = text;
    it[it.length - 1].appendChild(header);
    it.push(header);
    const innerList = elem(it, 'ul');
    it[it.length - 1].appendChild(innerList);
    it.push(innerList);
    if (noIndent) {
        innerList.classList.add('recursion');
    }
    const res = content();
    it.pop();
    it.pop();
    return res;
}
// ? MAIN ----------------------------------------------------------
function bcnfSolve(it, R) {
    if (!checkRelation(R))
        throw Error("The given relation is faulty.");
    printRelation(it, R);
    let title = `Checking whether ${R.name} is in BCNF:`;
    const bcnf = newSection(it, title, () => bcnfCheck(it, R));
    if (bcnf === undefined) {
        newSection(it, `Relation is in BCNF, returning...`, () => { });
        it.pop();
        return [R];
    }
    title = `Splitting into ${bcnf.rel1.name} and ${bcnf.rel2.name}:`;
    newSection(it, title, () => {
        let attributeStr = attribStr(bcnf.dets);
        let [rel1Attrbs, rel2Attrbs] = [attribStr(bcnf.rel1.attributes), attribStr(bcnf.rel2.attributes)];
        newLi(it, `${bcnf.rel1.name} = {${attributeStr}}<sup>+</sup> = {${rel1Attrbs}}`);
        newLi(it, `${bcnf.rel2.name} = {${attributeStr}} ∪ (R - {${attributeStr}}<sup>+</sup>) = {${rel2Attrbs}}`);
    });
    title = `Projecting FDs to ${bcnf.rel1.name} and ${bcnf.rel2.name}:`;
    newSection(it, title, () => {
        for (const rel of [bcnf.rel1, bcnf.rel2]) {
            const projectedFDs = projectFDs(rel);
            rel.fds = projectedFDs
                .filter((a) => a.minimal && a.deps.size > 0)
                .map(({ dets, deps }) => ({ dets, deps }));
            newLi(it, relationStr(rel), true);
            printFDs(it, projectedFDs);
            it.pop();
        }
    });
    title = `Recursively decomposing ${bcnf.rel1.name} and ${bcnf.rel2.name}:`;
    return newSection(it, title, () => {
        const res = [...bcnfSolve(it, bcnf.rel1), ...bcnfSolve(it, bcnf.rel2)];
        it.pop();
        return res;
    }, true);
}
function relationFromString(attrStr, fdStr) {
    const splitAndTrim = (str) => str.split(',').map((s) => s.trim());
    try {
        const newAttribs = new Set(splitAndTrim(attrStr));
        const FDs = fdStr.split(';').map((a) => {
            const [det, dep] = a.split('->');
            return { dets: new Set(splitAndTrim(det)), deps: new Set(splitAndTrim(dep)) };
        });
        return {
            name: 'R', fds: FDs,
            attributes: newAttribs,
        };
    }
    catch {
        throw Error("Parsing the relation failed.");
    }
}
function parseAndSolve() {
    const it = [document.getElementById('bcnf')];
    it[0].innerHTML = '';
    const attributeList = document.getElementById('attributes');
    const fdList = document.getElementById('fds');
    const relation = relationFromString(attributeList.value, fdList.value);
    const solutions = document.getElementById('solutions');
    solutions.innerHTML = '';
    const hiddenElements = document.getElementsByClassName('hidden');
    while (hiddenElements.length > 0)
        hiddenElements[0].classList.remove('hidden');
    for (const rel of bcnfSolve(it, relation)) {
        const listItem = elem(it, 'li');
        const relation = elem(it, 'div');
        const fds = elem(it, 'div');
        relation.innerHTML = relationStr(rel);
        fds.innerHTML = `FDs: {${fdsStr(combineFDs(rel.fds))}}`;
        listItem.appendChild(relation);
        listItem.style.paddingTop = '5px';
        listItem.appendChild(fds);
        solutions.appendChild(listItem);
    }
    return false;
}
