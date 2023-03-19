include "cv.mm"
include "ctcl.mm"
include "cfv.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cid.mm"
include "cun.mm"
include "wcel.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "whe.mm"
include "wfun.mm"
include "frege75.mm"
include "wn.mm"
include "wo.mm"
include "elun.mm"
include "df-or.mm"
include "cop.mm"
include "elexi.mm"
include "vex.mm"
include "elimasn.mm"
include "df-br.mm"
include "brcnv.mm"
include "3bitr2i.mm"
include "notbii.mm"
include "bitr4i.mm"
include "imbi12i.mm"
include "3bitri.mm"
include "imbi2i.mm"
include "albii.mm"
include "imbi1i.mm"
include "frege130.mm"
include "sylbi.mm"
include "ax-mp.mm"

theorem frege131
  let cR: class R
  let cU: class U
  let cM: class M
  let cV: class V
  let va: setvar a
  let vb: setvar b
  assume frege130.m: |- M e. U
  assume frege130.r: |- R e. V


  assert |- ( Fun `' `' R -> R hereditary ( ( `' ( t+ ` R ) " { M } ) u. ( ( ( t+ ` R ) u. _I ) " { M } ) ) )

  proof
    vb
    cv
    #
    cR
    ctcl
    cfv
    #
    ccnv
    #
    cM
    csn
    #
    cima
    #
    @1
    cid
    cun
    #
    @3
    cima
    #
    cun
    #
    wcel
    #
    @0
    va
    cv
    #
    cR
    wbr
    #
    @9
    @7
    wcel
    #
    wi
    #
    va
    wal
    #
    wi
    #
    vb
    wal
    #
    @7
    cR
    whe
    #
    wi
    #
    cR
    ccnv
    ccnv
    wfun
    @16
    wi
    #
    vb
    va
    @7
    cR
    frege75
    @17
    @0
    cM
    @1
    wbr
    #
    wn
    #
    cM
    @0
    @5
    wbr
    #
    wi
    #
    @10
    @9
    cM
    @1
    wbr
    #
    wn
    #
    cM
    @9
    @5
    wbr
    #
    wi
    #
    wi
    #
    va
    wal
    #
    wi
    #
    vb
    wal
    #
    @16
    wi
    @18
    @15
    @30
    @16
    @14
    @29
    vb
    @8
    @22
    @13
    @28
    @8
    @0
    @4
    wcel
    #
    @0
    @6
    wcel
    #
    wo
    @31
    wn
    #
    @32
    wi
    @22
    @0
    @4
    @6
    elun
    @31
    @32
    df-or
    @33
    @20
    @32
    @21
    @31
    @19
    @31
    cM
    @0
    cop
    #
    @2
    wcel
    cM
    @0
    @2
    wbr
    @19
    @2
    cM
    @0
    cM
    cU
    frege130.m
    elexi
    #
    vb
    vex
    #
    elimasn
    cM
    @0
    @2
    df-br
    cM
    @0
    @1
    @35
    @36
    brcnv
    3bitr2i
    notbii
    @32
    @34
    @5
    wcel
    @21
    @5
    cM
    @0
    @35
    @36
    elimasn
    cM
    @0
    @5
    df-br
    bitr4i
    imbi12i
    3bitri
    @12
    @27
    va
    @11
    @26
    @10
    @11
    @9
    @4
    wcel
    #
    @9
    @6
    wcel
    #
    wo
    @37
    wn
    #
    @38
    wi
    @26
    @9
    @4
    @6
    elun
    @37
    @38
    df-or
    @39
    @24
    @38
    @25
    @37
    @23
    @37
    cM
    @9
    cop
    #
    @2
    wcel
    cM
    @9
    @2
    wbr
    @23
    @2
    cM
    @9
    @35
    va
    vex
    #
    elimasn
    cM
    @9
    @2
    df-br
    cM
    @9
    @1
    @35
    @41
    brcnv
    3bitr2i
    notbii
    @38
    @40
    @5
    wcel
    @25
    @5
    cM
    @9
    @35
    @41
    elimasn
    cM
    @9
    @5
    df-br
    bitr4i
    imbi12i
    3bitri
    imbi2i
    albii
    imbi12i
    albii
    imbi1i
    cR
    cU
    cM
    cV
    va
    vb
    frege130.m
    frege130.r
    frege130
    sylbi
    ax-mp
end
