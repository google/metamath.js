include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cre.mm"
include "cfv.mm"
include "ci.mm"
include "cmul.mm"
include "crp.mm"
include "wnel.mm"
include "w3a.mm"
include "cc.mm"
include "wrex.mm"
include "wrmo.mm"
include "wreu.mm"
include "resqrex.mm"
include "recn.mm"
include "adantr.mm"
include "simprr.mm"
include "rere.mm"
include "breq2d.mm"
include "biimpar.mm"
include "adantrr.mm"
include "rennim.mm"
include "3jca.mm"
include "jca.mm"
include "reximi2.mm"
include "syl.mm"
include "sqrmo.mm"
include "reu5.mm"
include "sylanbrc.mm"

theorem resqreu
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( ( A e. RR /\ 0 <_ A ) -> E! x e. CC ( ( x ^ 2 ) = A /\ 0 <_ ( Re ` x ) /\ ( _i x. x ) e/ RR+ ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    vx
    cv
    #
    c2
    cexp
    co
    cA
    wceq
    #
    cc0
    @3
    cre
    cfv
    #
    cle
    wbr
    #
    ci
    @3
    cmul
    co
    crp
    wnel
    #
    w3a
    #
    vx
    cc
    wrex
    #
    @8
    vx
    cc
    wrmo
    #
    @8
    vx
    cc
    wreu
    @2
    cc0
    @3
    cle
    wbr
    #
    @4
    wa
    #
    vx
    cr
    wrex
    @9
    vx
    cA
    resqrex
    @12
    @8
    vx
    cr
    cc
    @3
    cr
    wcel
    #
    @12
    wa
    #
    @3
    cc
    wcel
    #
    @8
    @13
    @15
    @12
    @3
    recn
    adantr
    @14
    @4
    @6
    @7
    @13
    @11
    @4
    simprr
    @13
    @11
    @6
    @4
    @13
    @6
    @11
    @13
    @5
    @3
    cc0
    cle
    @3
    rere
    breq2d
    biimpar
    adantrr
    @13
    @7
    @12
    @3
    rennim
    adantr
    3jca
    jca
    reximi2
    syl
    @2
    cA
    cc
    wcel
    #
    @10
    @0
    @16
    @1
    cA
    recn
    adantr
    vx
    cA
    sqrmo
    syl
    @8
    vx
    cc
    reu5
    sylanbrc
end
