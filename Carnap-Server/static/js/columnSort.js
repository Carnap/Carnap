function isNumeral (c) { return /^\d+$/.test(c) }

function numeralChunks (a) {
    var buffer = []
    var chunking = false
    for (var x = 0; x < a.length; x++) {
        let theChar = a.charAt(x)
        if (!isNumeral(theChar)) {
           chunking = false;
           buffer.push([theChar])
        } else if (chunking) {
           buffer[buffer.length - 1].push(theChar)
        } else {
           chunking = true;
           buffer.push([theChar])
        }
    }
    return buffer
}

function compareByChunks(a,b) {
    const chunksA = numeralChunks(a)
    const chunksB = numeralChunks(b)
    for (var x = 0; x < Math.min(chunksA.length, chunksB.length); x++) {
        //if the first characters are numerals, then the chunk should be entirely numerals
        //and we compare those
        if (isNumeral(chunksA[x][0]) && isNumeral(chunksB[x][0])) {
            let intA = parseInt(chunksA[x].join(''),10)
            let intB = parseInt(chunksB[x].join(''),10)
            if (intA > intB) return 1
            if (intA < intB) return -1
        }
        //otherwise, we compare as arrays
        if (chunksA[x] > chunksB[x]) return 1
        if (chunksA[x] < chunksB[x]) return -1
    }
    //if the loop finishes, one of these is a prefix of the other, or they're
    //the same, so we compare length
    if (chunksA.length > chunksB.length) return 1
    if (chunksA.length < chunksB.length) return -1
    //and the only possibility remaining is that they're the same.
    return 0
}

function sortByCol(elt,num) {
    let table = elt.closest("table")
    let body = table.querySelector("tbody")
    let head = table.querySelector("thead")
    let rows = Array.from(body.children)
    let headers = head.getElementsByTagName("th")
    headers[num].upsorted = (headers[num].upsorted * -1) || 1
    let upsort = headers[num].upsorted
    let sortedRows = rows.sort((a,b) => {
        let val1 = a.children[num].innerText.toLowerCase()
        let val2 = b.children[num].innerText.toLowerCase()
        return compareByChunks(val1, val2) * upsort
    })
    sortedRows.forEach(el => body.appendChild(el))
}

