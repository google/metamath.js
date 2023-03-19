include "ctcl.mm"
include "cfv.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cid.mm"
include "cun.mm"
include "whe.mm"
include "wcel.mm"
include "wbr.mm"
include "wi.mm"
include "wfun.mm"
include "wn.mm"
include "cvv.mm"
include "fvex.mm"
include "cnvex.mm"
include "imaexg.mm"
include "ax-mp.mm"
include "imaundir.mm"
include "imai.mm"
include "snex.mm"
include "eqeltri.mm"
include "unex.mm"
include "frege83.mm"
include "cop.mm"
include "elexi.mm"
include "elimasn.mm"
include "df-br.mm"
include "brcnv.mm"
include "3bitr2i.mm"
include "wo.mm"
include "elun.mm"
include "df-or.mm"
include "notbii.mm"
include "bitr4i.mm"
include "imbi12i.mm"
include "3bitri.mm"
include "imbi2i.mm"
include "frege132.mm"
include "sylbi.mm"

theorem frege133
  let cR: class R
  let cS: class S
  let cU: class U
  let cM: class M
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume frege133.x: |- X e. U
  assume frege133.y: |- Y e. V
  assume frege133.m: |- M e. W
  assume frege133.r: |- R e. S


  assert |- ( Fun `' `' R -> ( X ( t+ ` R ) M -> ( X ( t+ ` R ) Y -> ( -. Y ( t+ ` R ) M -> M ( ( t+ ` R ) u. _I ) Y ) ) ) )

  proof
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
    @0
    cid
    cun
    #
    @2
    cima
    #
    cun
    #
    cR
    whe
    #
    cX
    @3
    wcel
    #
    cX
    cY
    @0
    wbr
    #
    cY
    @6
    wcel
    #
    wi
    #
    wi
    #
    wi
    #
    cR
    ccnv
    ccnv
    wfun
    cX
    cM
    @0
    wbr
    #
    @9
    cY
    cM
    @0
    wbr
    #
    wn
    #
    cM
    cY
    @4
    wbr
    #
    wi
    #
    wi
    #
    wi
    #
    wi
    #
    @3
    @5
    cR
    cU
    cV
    cS
    cvv
    cvv
    cX
    cY
    frege133.x
    frege133.y
    frege133.r
    @1
    cvv
    wcel
    @3
    cvv
    wcel
    @0
    cR
    ctcl
    fvex
    #
    cnvex
    @1
    @2
    cvv
    imaexg
    ax-mp
    @5
    @0
    @2
    cima
    #
    cid
    @2
    cima
    #
    cun
    cvv
    @0
    cid
    @2
    imaundir
    @23
    @24
    @0
    cvv
    wcel
    @23
    cvv
    wcel
    @22
    @0
    @2
    cvv
    imaexg
    ax-mp
    @24
    @2
    cvv
    @2
    imai
    cM
    snex
    eqeltri
    unex
    eqeltri
    frege83
    @13
    @7
    @20
    wi
    @21
    @12
    @20
    @7
    @8
    @14
    @11
    @19
    @8
    cM
    cX
    cop
    @1
    wcel
    cM
    cX
    @1
    wbr
    @14
    @1
    cM
    cX
    cM
    cW
    frege133.m
    elexi
    #
    cX
    cU
    frege133.x
    elexi
    #
    elimasn
    cM
    cX
    @1
    df-br
    cM
    cX
    @0
    @25
    @26
    brcnv
    3bitr2i
    @10
    @18
    @9
    @10
    cY
    @3
    wcel
    #
    cY
    @5
    wcel
    #
    wo
    @27
    wn
    #
    @28
    wi
    @18
    cY
    @3
    @5
    elun
    @27
    @28
    df-or
    @29
    @16
    @28
    @17
    @27
    @15
    @27
    cM
    cY
    cop
    #
    @1
    wcel
    cM
    cY
    @1
    wbr
    @15
    @1
    cM
    cY
    @25
    cY
    cV
    frege133.y
    elexi
    #
    elimasn
    cM
    cY
    @1
    df-br
    cM
    cY
    @0
    @25
    @31
    brcnv
    3bitr2i
    notbii
    @28
    @30
    @4
    wcel
    @17
    @4
    cM
    cY
    @25
    @31
    elimasn
    cM
    cY
    @4
    df-br
    bitr4i
    imbi12i
    3bitri
    imbi2i
    imbi12i
    imbi2i
    cR
    cW
    cM
    cS
    cX
    cY
    frege133.m
    frege133.r
    frege132
    sylbi
    ax-mp
end
