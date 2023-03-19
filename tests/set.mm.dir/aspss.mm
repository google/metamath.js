include "casa.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "csubrg.mm"
include "cfv.mm"
include "clss.mm"
include "cin.mm"
include "crab.mm"
include "cint.mm"
include "wa.mm"
include "wi.mm"
include "simpl3.mm"
include "sstr2.mm"
include "syl.mm"
include "ss2rabdv.mm"
include "intss.mm"
include "wceq.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2.mm"
include "sstrd.mm"
include "eqid.mm"
include "aspval.mm"
include "syl2anc.mm"
include "3adant3.mm"
include "3sstr4d.mm"

theorem aspss
  let cA: class A
  let cS: class S
  let cT: class T
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let cL: class L
  assume aspval.a: |- A = ( AlgSpan ` W )
  assume aspval.v: |- V = ( Base ` W )


  assert |- ( ( W e. AssAlg /\ S C_ V /\ T C_ S ) -> ( A ` T ) C_ ( A ` S ) )

  proof
    cW
    casa
    wcel
    #
    cS
    cV
    wss
    #
    cT
    cS
    wss
    #
    w3a
    #
    cT
    vt
    cv
    #
    wss
    #
    vt
    cW
    csubrg
    cfv
    cW
    clss
    cfv
    #
    cin
    #
    crab
    #
    cint
    #
    cS
    @4
    wss
    #
    vt
    @7
    crab
    #
    cint
    #
    cT
    cA
    cfv
    #
    cS
    cA
    cfv
    #
    @3
    @11
    @8
    wss
    @9
    @12
    wss
    @3
    @10
    @5
    vt
    @7
    @3
    @4
    @7
    wcel
    #
    wa
    @2
    @10
    @5
    wi
    @0
    @1
    @2
    @15
    simpl3
    cT
    cS
    @4
    sstr2
    syl
    ss2rabdv
    @11
    @8
    intss
    syl
    @3
    @0
    cT
    cV
    wss
    @13
    @9
    wceq
    @0
    @1
    @2
    simp1
    @3
    cT
    cS
    cV
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    simp2
    sstrd
    vt
    cA
    cT
    @6
    cV
    cW
    aspval.a
    aspval.v
    @6
    eqid
    #
    aspval
    syl2anc
    @0
    @1
    @14
    @12
    wceq
    @2
    vt
    cA
    cS
    @6
    cV
    cW
    aspval.a
    aspval.v
    @16
    aspval
    3adant3
    3sstr4d
end
