include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "clss.mm"
include "cfv.mm"
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
include "lspval.mm"
include "syl2anc.mm"
include "3adant3.mm"
include "3sstr4d.mm"

theorem lspss
  let cT: class T
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let vt: setvar t
  assume lspss.v: |- V = ( Base ` W )
  assume lspss.n: |- N = ( LSpan ` W )


  assert |- ( ( W e. LMod /\ U C_ V /\ T C_ U ) -> ( N ` T ) C_ ( N ` U ) )

  proof
    cW
    clmod
    wcel
    #
    cU
    cV
    wss
    #
    cT
    cU
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
    clss
    cfv
    #
    crab
    #
    cint
    #
    cU
    @4
    wss
    #
    vt
    @6
    crab
    #
    cint
    #
    cT
    cN
    cfv
    #
    cU
    cN
    cfv
    #
    @3
    @10
    @7
    wss
    @8
    @11
    wss
    @3
    @9
    @5
    vt
    @6
    @3
    @4
    @6
    wcel
    #
    wa
    @2
    @9
    @5
    wi
    @0
    @1
    @2
    @14
    simpl3
    cT
    cU
    @4
    sstr2
    syl
    ss2rabdv
    @10
    @7
    intss
    syl
    @3
    @0
    cT
    cV
    wss
    @12
    @8
    wceq
    @0
    @1
    @2
    simp1
    @3
    cT
    cU
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
    @6
    cT
    cN
    cV
    cW
    lspss.v
    @6
    eqid
    #
    lspss.n
    lspval
    syl2anc
    @0
    @1
    @13
    @11
    wceq
    @2
    vt
    @6
    cU
    cN
    cV
    cW
    lspss.v
    @15
    lspss.n
    lspval
    3adant3
    3sstr4d
end
