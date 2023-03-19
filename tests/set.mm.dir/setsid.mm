include "wcel.mm"
include "wa.mm"
include "cnx.mm"
include "cfv.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cun.mm"
include "setsval.mm"
include "fveq2d.mm"
include "resexg.mm"
include "adantr.mm"
include "snex.mm"
include "unexg.mm"
include "sylancl.mm"
include "strfvnd.mm"
include "wceq.mm"
include "fvex.mm"
include "snid.mm"
include "fvres.mm"
include "ax-mp.mm"
include "c0.mm"
include "cin.mm"
include "resres.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "reseq2i.mm"
include "res0.mm"
include "a1i.mm"
include "wrel.mm"
include "cdm.mm"
include "wss.mm"
include "cxp.mm"
include "elex.mm"
include "adantl.mm"
include "opelxpi.mm"
include "sylancr.mm"
include "opex.mm"
include "relsn.mm"
include "sylibr.mm"
include "dmsnopss.mm"
include "relssres.mm"
include "uneq12d.mm"
include "resundir.mm"
include "un0.mm"
include "uncom.mm"
include "eqtr3i.mm"
include "3eqtr4g.mm"
include "fveq1d.mm"
include "syl5eqr.mm"
include "fvsng.mm"
include "sylancom.mm"
include "eqtrd.mm"
include "3eqtrrd.mm"

theorem setsid
  let cA: class A
  let cC: class C
  let cE: class E
  let cV: class V
  let cW: class W
  assume setsid.e: |- E = Slot ( E ` ndx )


  assert |- ( ( W e. A /\ C e. V ) -> C = ( E ` ( W sSet <. ( E ` ndx ) , C >. ) ) )

  proof
    cW
    cA
    wcel
    #
    cC
    cV
    wcel
    #
    wa
    #
    cW
    cnx
    cE
    cfv
    #
    cC
    cop
    #
    csts
    co
    #
    cE
    cfv
    cW
    cvv
    @3
    csn
    #
    cdif
    #
    cres
    #
    @4
    csn
    #
    cun
    #
    cE
    cfv
    @3
    @10
    cfv
    #
    cC
    @2
    @5
    @10
    cE
    @3
    cC
    cW
    cA
    cV
    setsval
    fveq2d
    @2
    @10
    cE
    @3
    cvv
    setsid.e
    @2
    @8
    cvv
    wcel
    #
    @9
    cvv
    wcel
    @10
    cvv
    wcel
    @0
    @12
    @1
    cW
    @7
    cA
    resexg
    adantr
    @4
    snex
    @8
    @9
    cvv
    cvv
    unexg
    sylancl
    strfvnd
    @2
    @11
    @3
    @9
    cfv
    #
    cC
    @2
    @11
    @3
    @10
    @6
    cres
    #
    cfv
    #
    @13
    @3
    @6
    wcel
    @15
    @11
    wceq
    @3
    cnx
    cE
    fvex
    #
    snid
    @3
    @6
    @10
    fvres
    ax-mp
    @2
    @3
    @14
    @9
    @2
    @8
    @6
    cres
    #
    @9
    @6
    cres
    #
    cun
    c0
    @9
    cun
    #
    @14
    @9
    @2
    @17
    c0
    @18
    @9
    @17
    c0
    wceq
    @2
    @17
    cW
    @7
    @6
    cin
    #
    cres
    #
    c0
    cW
    @7
    @6
    resres
    @21
    cW
    c0
    cres
    c0
    @20
    c0
    cW
    @20
    @6
    @7
    cin
    c0
    @7
    @6
    incom
    @6
    cvv
    disjdif
    eqtri
    reseq2i
    cW
    res0
    eqtri
    eqtri
    a1i
    @2
    @9
    wrel
    #
    @9
    cdm
    @6
    wss
    @18
    @9
    wceq
    @2
    @4
    cvv
    cvv
    cxp
    wcel
    #
    @22
    @2
    @3
    cvv
    wcel
    #
    cC
    cvv
    wcel
    #
    @23
    @16
    @1
    @25
    @0
    cC
    cV
    elex
    adantl
    @3
    cC
    cvv
    cvv
    opelxpi
    sylancr
    @4
    @3
    cC
    opex
    relsn
    sylibr
    @3
    cC
    dmsnopss
    @9
    @6
    relssres
    sylancl
    uneq12d
    @8
    @9
    @6
    resundir
    @9
    c0
    cun
    @9
    @19
    @9
    un0
    @9
    c0
    uncom
    eqtr3i
    3eqtr4g
    fveq1d
    syl5eqr
    @0
    @1
    @24
    @13
    cC
    wceq
    @24
    @2
    @16
    a1i
    @3
    cC
    cvv
    cV
    fvsng
    sylancom
    eqtrd
    3eqtrrd
end
