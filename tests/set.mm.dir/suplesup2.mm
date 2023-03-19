include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wrex.mm"
include "w3a.mm"
include "sselda.mm"
include "3ad2ant1.mm"
include "simp1l.mm"
include "simp2.mm"
include "syl2anc.mm"
include "wss.mm"
include "supxrcl.mm"
include "syl.mm"
include "simp3.mm"
include "adantr.mm"
include "simpr.mm"
include "supxrub.mm"
include "xrletrd.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "wb.mm"
include "supxrleub.mm"
include "mpbird.mm"

theorem suplesup2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume suplesup2.a: |- ( ph -> A C_ RR* )
  assume suplesup2.b: |- ( ph -> B C_ RR* )
  assume suplesup2.c: |- ( ( ph /\ x e. A ) -> E. y e. B x <_ y )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> sup ( A , RR* , < ) <_ sup ( B , RR* , < ) )

  proof
    wph
    cA
    cxr
    clt
    csup
    cB
    cxr
    clt
    csup
    #
    cle
    wbr
    #
    vx
    cv
    #
    @0
    cle
    wbr
    #
    vx
    cA
    wral
    #
    wph
    @3
    vx
    cA
    wph
    @2
    cA
    wcel
    #
    wa
    #
    @2
    vy
    cv
    #
    cle
    wbr
    #
    vy
    cB
    wrex
    @3
    suplesup2.c
    @6
    @8
    @3
    vy
    cB
    @6
    @7
    cB
    wcel
    #
    @8
    @3
    @6
    @9
    @8
    w3a
    #
    @2
    @7
    @0
    @6
    @9
    @2
    cxr
    wcel
    @8
    wph
    cA
    cxr
    @2
    suplesup2.a
    sselda
    3ad2ant1
    @10
    wph
    @9
    @7
    cxr
    wcel
    wph
    @5
    @9
    @8
    simp1l
    #
    @6
    @9
    @8
    simp2
    #
    wph
    cB
    cxr
    @7
    suplesup2.b
    sselda
    syl2anc
    @10
    wph
    @0
    cxr
    wcel
    #
    @11
    wph
    cB
    cxr
    wss
    #
    @13
    suplesup2.b
    cB
    supxrcl
    syl
    #
    syl
    @6
    @9
    @8
    simp3
    @10
    wph
    @9
    @7
    @0
    cle
    wbr
    #
    @11
    @12
    wph
    @9
    wa
    @14
    @9
    @16
    wph
    @14
    @9
    suplesup2.b
    adantr
    wph
    @9
    simpr
    cB
    @7
    supxrub
    syl2anc
    syl2anc
    xrletrd
    3exp
    rexlimdv
    mpd
    ralrimiva
    wph
    cA
    cxr
    wss
    @13
    @1
    @4
    wb
    suplesup2.a
    @15
    vx
    cA
    @0
    supxrleub
    syl2anc
    mpbird
end
