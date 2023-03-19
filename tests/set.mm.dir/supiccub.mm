include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wcel.mm"
include "clt.mm"
include "csup.mm"
include "cicc.mm"
include "co.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "sstrd.mm"
include "wa.mm"
include "cxr.mm"
include "adantr.mm"
include "rexrd.mm"
include "sselda.mm"
include "iccleub.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "suprub.mm"
include "syl31anc.mm"

theorem supiccub
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  assume supicc.1: |- ( ph -> B e. RR )
  assume supicc.2: |- ( ph -> C e. RR )
  assume supicc.3: |- ( ph -> A C_ ( B [,] C ) )
  assume supicc.4: |- ( ph -> A =/= (/) )
  assume supiccub.1: |- ( ph -> D e. A )


  assert |- ( ph -> D <_ sup ( A , RR , < ) )

  proof
    wph
    cA
    cr
    wss
    cA
    c0
    wne
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vy
    cr
    wrex
    #
    cD
    cA
    wcel
    cD
    cA
    cr
    clt
    csup
    cle
    wbr
    wph
    cA
    cB
    cC
    cicc
    co
    #
    cr
    supicc.3
    wph
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    @5
    cr
    wss
    supicc.1
    supicc.2
    cB
    cC
    iccssre
    syl2anc
    sstrd
    supicc.4
    wph
    @7
    @0
    cC
    cle
    wbr
    #
    vx
    cA
    wral
    #
    @4
    supicc.2
    wph
    @8
    vx
    cA
    wph
    @0
    cA
    wcel
    #
    wa
    #
    cB
    cxr
    wcel
    cC
    cxr
    wcel
    @0
    @5
    wcel
    @8
    @11
    cB
    wph
    @6
    @10
    supicc.1
    adantr
    rexrd
    @11
    cC
    wph
    @7
    @10
    supicc.2
    adantr
    rexrd
    wph
    cA
    @5
    @0
    supicc.3
    sselda
    cB
    cC
    @0
    iccleub
    syl3anc
    ralrimiva
    @3
    @9
    vy
    cC
    cr
    @1
    cC
    wceq
    @2
    @8
    vx
    cA
    @1
    cC
    @0
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    supiccub.1
    vy
    vx
    cA
    cD
    suprub
    syl31anc
end
