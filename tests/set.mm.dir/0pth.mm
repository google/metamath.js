include "wcel.mm"
include "c0.mm"
include "cpths.mm"
include "cfv.mm"
include "wbr.mm"
include "ctrls.mm"
include "c1.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cres.mm"
include "ccnv.mm"
include "wfun.mm"
include "cc0.mm"
include "cpr.mm"
include "cima.mm"
include "cin.mm"
include "wceq.mm"
include "w3a.mm"
include "cfz.mm"
include "wf.mm"
include "wb.mm"
include "ispth.mm"
include "a1i.mm"
include "wa.mm"
include "3anass.mm"
include "funcnv0.mm"
include "cle.mm"
include "hash0.mm"
include "0le1.mm"
include "eqbrtri.mm"
include "cz.mm"
include "1z.mm"
include "0z.mm"
include "eqeltri.mm"
include "fzon.mm"
include "mp2an.mm"
include "mpbi.mm"
include "reseq2i.mm"
include "res0.mm"
include "eqtri.mm"
include "cnveqi.mm"
include "funeqi.mm"
include "mpbir.mm"
include "imaeq2i.mm"
include "ima0.mm"
include "ineq2i.mm"
include "in0.mm"
include "pm3.2i.mm"
include "biantru.mm"
include "syl6bbr.mm"
include "0trl.mm"
include "3bitrd.mm"

theorem 0pth
  let cP: class P
  let cG: class G
  let cV: class V
  let cW: class W
  assume 0pth.v: |- V = ( Vtx ` G )


  assert |- ( G e. W -> ( (/) ( Paths ` G ) P <-> P : ( 0 ... 0 ) --> V ) )

  proof
    cG
    cW
    wcel
    #
    c0
    cP
    cG
    cpths
    cfv
    wbr
    #
    c0
    cP
    cG
    ctrls
    cfv
    wbr
    #
    cP
    c1
    c0
    chash
    cfv
    #
    cfzo
    co
    #
    cres
    #
    ccnv
    #
    wfun
    #
    cP
    cc0
    @3
    cpr
    cima
    #
    cP
    @4
    cima
    #
    cin
    #
    c0
    wceq
    #
    w3a
    #
    @2
    cc0
    cc0
    cfz
    co
    cV
    cP
    wf
    @1
    @12
    wb
    @0
    cP
    c0
    cG
    ispth
    a1i
    @0
    @12
    @2
    @7
    @11
    wa
    #
    wa
    #
    @2
    @12
    @14
    wb
    @0
    @2
    @7
    @11
    3anass
    a1i
    @13
    @2
    @7
    @11
    @7
    c0
    ccnv
    #
    wfun
    funcnv0
    @6
    @15
    @5
    c0
    @5
    cP
    c0
    cres
    c0
    @4
    c0
    cP
    @3
    c1
    cle
    wbr
    #
    @4
    c0
    wceq
    #
    @3
    cc0
    c1
    cle
    hash0
    0le1
    eqbrtri
    c1
    cz
    wcel
    @3
    cz
    wcel
    @16
    @17
    wb
    1z
    @3
    cc0
    cz
    hash0
    0z
    eqeltri
    c1
    @3
    fzon
    mp2an
    mpbi
    #
    reseq2i
    cP
    res0
    eqtri
    cnveqi
    funeqi
    mpbir
    @10
    @8
    c0
    cin
    c0
    @9
    c0
    @8
    @9
    cP
    c0
    cima
    c0
    @4
    c0
    cP
    @18
    imaeq2i
    cP
    ima0
    eqtri
    ineq2i
    @8
    in0
    eqtri
    pm3.2i
    biantru
    syl6bbr
    cP
    cW
    cG
    cV
    0pth.v
    0trl
    3bitrd
end
