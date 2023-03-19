include "cun.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cres.mm"
include "cxad.mm"
include "co.mm"
include "eqid.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "adantlr.mm"
include "wn.mm"
include "simpll.mm"
include "elunnel1.mm"
include "adantll.mm"
include "syl2anc.mm"
include "pm2.61dan.mm"
include "fmptdf.mm"
include "sge0split.mm"
include "wceq.mm"
include "ssun1.mm"
include "resmpti.mm"
include "fveq2i.mm"
include "ssun2.mm"
include "oveq12i.mm"
include "a1i.mm"
include "eqtrd.mm"

theorem sge0splitmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let vk: setvar k
  assume sge0splitmpt.xph: |- F/ x ph
  assume sge0splitmpt.a: |- ( ph -> A e. V )
  assume sge0splitmpt.b: |- ( ph -> B e. W )
  assume sge0splitmpt.in: |- ( ph -> ( A i^i B ) = (/) )
  assume sge0splitmpt.ac: |- ( ( ph /\ x e. A ) -> C e. ( 0 [,] +oo ) )
  assume sge0splitmpt.bc: |- ( ( ph /\ x e. B ) -> C e. ( 0 [,] +oo ) )

  disjoint A x
  disjoint B x
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( x e. ( A u. B ) |-> C ) ) = ( ( sum^ ` ( x e. A |-> C ) ) +e ( sum^ ` ( x e. B |-> C ) ) ) )

  proof
    wph
    vx
    cA
    cB
    cun
    #
    cC
    cmpt
    #
    csumge0
    cfv
    @1
    cA
    cres
    #
    csumge0
    cfv
    #
    @1
    cB
    cres
    #
    csumge0
    cfv
    #
    cxad
    co
    #
    vx
    cA
    cC
    cmpt
    #
    csumge0
    cfv
    #
    vx
    cB
    cC
    cmpt
    #
    csumge0
    cfv
    #
    cxad
    co
    #
    wph
    cA
    cB
    @0
    @1
    cV
    cW
    sge0splitmpt.a
    sge0splitmpt.b
    @0
    eqid
    sge0splitmpt.in
    wph
    vx
    @0
    cC
    cc0
    cpnf
    cicc
    co
    #
    @1
    sge0splitmpt.xph
    wph
    vx
    cv
    #
    @0
    wcel
    #
    wa
    #
    @13
    cA
    wcel
    #
    cC
    @12
    wcel
    #
    wph
    @16
    @17
    @14
    sge0splitmpt.ac
    adantlr
    @15
    @16
    wn
    #
    wa
    wph
    @13
    cB
    wcel
    #
    @17
    wph
    @14
    @18
    simpll
    @14
    @18
    @19
    wph
    @13
    cA
    cB
    elunnel1
    adantll
    sge0splitmpt.bc
    syl2anc
    pm2.61dan
    @1
    eqid
    fmptdf
    sge0split
    @6
    @11
    wceq
    wph
    @3
    @8
    @5
    @10
    cxad
    @2
    @7
    csumge0
    vx
    @0
    cA
    cC
    cA
    cB
    ssun1
    resmpti
    fveq2i
    @4
    @9
    csumge0
    vx
    @0
    cB
    cC
    cB
    cA
    ssun2
    resmpti
    fveq2i
    oveq12i
    a1i
    eqtrd
end
