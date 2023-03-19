include "ciun.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cres.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "adantr.mm"
include "3adant3.mm"
include "wss.mm"
include "wa.mm"
include "ssiun2.mm"
include "adantl.mm"
include "eqcomi.mm"
include "syl6sseq.mm"
include "simp3.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "sge0iunmpt.mm"
include "wb.mm"
include "feq2i.mm"
include "a1i.mm"
include "mpbid.mm"
include "feqmptd.mm"
include "fveq2d.mm"
include "fssresd.mm"
include "wceq.mm"
include "fvres.mm"
include "mpteq2ia.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "3eqtr4d.mm"

theorem sge0iun
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let vy: setvar y
  let vk: setvar k
  assume sge0iun.a: |- ( ph -> A e. V )
  assume sge0iun.b: |- ( ( ph /\ x e. A ) -> B e. W )
  assume sge0iun.x: |- X = U_ x e. A B
  assume sge0iun.f: |- ( ph -> F : X --> ( 0 [,] +oo ) )
  assume sge0iun.dj: |- ( ph -> Disj_ x e. A B )

  disjoint A x
  disjoint F x
  disjoint W x
  disjoint ph x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint F y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( sum^ ` F ) = ( sum^ ` ( x e. A |-> ( sum^ ` ( F |` B ) ) ) ) )

  proof
    wph
    vy
    vx
    cA
    cB
    ciun
    #
    vy
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    vx
    cA
    vy
    cB
    @2
    cmpt
    #
    csumge0
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    cF
    csumge0
    cfv
    vx
    cA
    cF
    cB
    cres
    #
    csumge0
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    wph
    vx
    cA
    cB
    @2
    vy
    cV
    cW
    sge0iun.a
    sge0iun.b
    sge0iun.dj
    wph
    vx
    cv
    cA
    wcel
    #
    @1
    cB
    wcel
    #
    w3a
    #
    cX
    cc0
    cpnf
    cicc
    co
    #
    @1
    cF
    wph
    @10
    cX
    @13
    cF
    wf
    #
    @11
    wph
    @14
    @10
    sge0iun.f
    adantr
    #
    3adant3
    @12
    cB
    cX
    @1
    wph
    @10
    cB
    cX
    wss
    @11
    wph
    @10
    wa
    #
    cB
    @0
    cX
    @10
    cB
    @0
    wss
    wph
    vx
    cA
    cB
    ssiun2
    adantl
    cX
    @0
    sge0iun.x
    eqcomi
    syl6sseq
    #
    3adant3
    wph
    @10
    @11
    simp3
    sseldd
    ffvelrnd
    sge0iunmpt
    wph
    cF
    @3
    csumge0
    wph
    vy
    @0
    @13
    cF
    wph
    @14
    @0
    @13
    cF
    wf
    #
    sge0iun.f
    @14
    @18
    wb
    wph
    cX
    @0
    @13
    cF
    sge0iun.x
    feq2i
    a1i
    mpbid
    feqmptd
    fveq2d
    wph
    @9
    @6
    csumge0
    wph
    vx
    cA
    @8
    @5
    @16
    @7
    @4
    csumge0
    @16
    @7
    vy
    cB
    @1
    @7
    cfv
    #
    cmpt
    #
    @4
    @16
    vy
    cB
    @13
    @7
    @16
    cX
    @13
    cB
    cF
    @15
    @17
    fssresd
    feqmptd
    @20
    @4
    wceq
    @16
    vy
    cB
    @19
    @2
    @1
    cB
    cF
    fvres
    mpteq2ia
    a1i
    eqtrd
    fveq2d
    mpteq2dva
    fveq2d
    3eqtr4d
end
