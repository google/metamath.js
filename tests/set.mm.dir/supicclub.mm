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
include "wb.mm"
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
include "sseldd.mm"
include "suprlub.mm"
include "syl31anc.mm"

theorem supicclub
  let wph: wff ph
  let vz: setvar z
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

  disjoint A z
  disjoint D z
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint C x
  disjoint C y
  disjoint ph x
  assert |- ( ph -> ( D < sup ( A , RR , < ) <-> E. z e. A D < z ) )

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
    cr
    wcel
    cD
    cA
    cr
    clt
    csup
    clt
    wbr
    cD
    vz
    cv
    clt
    wbr
    vz
    cA
    wrex
    wb
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
    #
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
    @9
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
    @9
    @12
    cB
    wph
    @6
    @11
    supicc.1
    adantr
    rexrd
    @12
    cC
    wph
    @7
    @11
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
    @10
    vy
    cC
    cr
    @1
    cC
    wceq
    @2
    @9
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
    wph
    cA
    cr
    cD
    @8
    supiccub.1
    sseldd
    vy
    vx
    vz
    cA
    cD
    suprlub
    syl31anc
end
