include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "cun.mm"
include "cvv.mm"
include "wss.mm"
include "wcel.mm"
include "ssexg.mm"
include "syl2anc.mm"
include "difexg.mm"
include "syl.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "disjdif.mm"
include "a1i.mm"
include "cv.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "0e0iccpnf.mm"
include "eqeltrd.mm"
include "sge0splitmpt.mm"
include "eqcomd.mm"
include "mpteq2da.mm"
include "fveq2d.mm"
include "sge0z.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "cxr.mm"
include "eqid.mm"
include "fmptdf.mm"
include "sge0xrcl.mm"
include "xaddid1.mm"
include "eqidd.mm"
include "3eqtrrd.mm"
include "undif.mm"
include "sylib.mm"
include "mpteq1d.mm"
include "3eqtr4d.mm"

theorem sge0ss
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  let vx: setvar x
  assume sge0ss.kph: |- F/ k ph
  assume sge0ss.b: |- ( ph -> B e. V )
  assume sge0ss.a: |- ( ph -> A C_ B )
  assume sge0ss.c: |- ( ( ph /\ k e. A ) -> C e. ( 0 [,] +oo ) )
  assume sge0ss.c0: |- ( ( ph /\ k e. ( B \ A ) ) -> C = 0 )

  disjoint A k
  disjoint B k
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( k e. A |-> C ) ) = ( sum^ ` ( k e. B |-> C ) ) )

  proof
    wph
    vk
    cA
    cC
    cmpt
    #
    csumge0
    cfv
    #
    vk
    cB
    cA
    cdif
    #
    cC
    cmpt
    #
    csumge0
    cfv
    #
    cxad
    co
    #
    vk
    cA
    @2
    cun
    #
    cC
    cmpt
    #
    csumge0
    cfv
    #
    @1
    vk
    cB
    cC
    cmpt
    #
    csumge0
    cfv
    wph
    @8
    @5
    wph
    vk
    cA
    @2
    cC
    cvv
    cvv
    sge0ss.kph
    wph
    cA
    cB
    wss
    #
    cB
    cV
    wcel
    #
    cA
    cvv
    wcel
    sge0ss.a
    sge0ss.b
    cA
    cB
    cV
    ssexg
    syl2anc
    #
    wph
    @11
    @2
    cvv
    wcel
    sge0ss.b
    cB
    cA
    cV
    difexg
    syl
    #
    cA
    @2
    cin
    c0
    wceq
    wph
    cA
    cB
    disjdif
    a1i
    sge0ss.c
    wph
    vk
    cv
    @2
    wcel
    wa
    #
    cC
    cc0
    cc0
    cpnf
    cicc
    co
    #
    sge0ss.c0
    cc0
    @15
    wcel
    @14
    0e0iccpnf
    a1i
    eqeltrd
    sge0splitmpt
    eqcomd
    wph
    @5
    @1
    cc0
    cxad
    co
    #
    @1
    @1
    wph
    @4
    cc0
    @1
    cxad
    wph
    @4
    vk
    @2
    cc0
    cmpt
    #
    csumge0
    cfv
    cc0
    wph
    @3
    @17
    csumge0
    wph
    vk
    @2
    cC
    cc0
    sge0ss.kph
    sge0ss.c0
    mpteq2da
    fveq2d
    wph
    @2
    vk
    cvv
    sge0ss.kph
    @13
    sge0z
    eqtrd
    oveq2d
    wph
    @1
    cxr
    wcel
    @16
    @1
    wceq
    wph
    @0
    cvv
    cA
    @12
    wph
    vk
    cA
    cC
    @15
    @0
    sge0ss.kph
    sge0ss.c
    @0
    eqid
    fmptdf
    sge0xrcl
    @1
    xaddid1
    syl
    wph
    @1
    eqidd
    3eqtrrd
    wph
    @9
    @7
    csumge0
    wph
    vk
    cB
    @6
    cC
    wph
    @6
    cB
    wph
    @10
    @6
    cB
    wceq
    sge0ss.a
    cA
    cB
    undif
    sylib
    eqcomd
    mpteq1d
    fveq2d
    3eqtr4d
end
