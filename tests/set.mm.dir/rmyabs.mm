include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "crmy.mm"
include "co.mm"
include "cneg.mm"
include "cabs.mm"
include "cz.mm"
include "wa.mm"
include "frmy.mm"
include "fovcl.mm"
include "zred.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "crmx.mm"
include "clt.mm"
include "cn0.mm"
include "simp1.mm"
include "elnn0z.mm"
include "biimpri.mm"
include "3adant1.mm"
include "rmxypos.mm"
include "syl2anc.mm"
include "simprd.mm"
include "rmyneg.mm"
include "oveq2.mm"
include "oddcomabszz.mm"

theorem rmyabs
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ B e. ZZ ) -> ( abs ` ( A rmY B ) ) = ( A rmY ( abs ` B ) ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    va
    vb
    cA
    va
    cv
    #
    crmy
    co
    #
    cA
    vb
    cv
    #
    crmy
    co
    cA
    @4
    cneg
    #
    crmy
    co
    cB
    cA
    cB
    crmy
    co
    cA
    cB
    cabs
    cfv
    #
    crmy
    co
    @1
    @2
    cz
    wcel
    #
    wa
    @3
    cA
    @2
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    zred
    @1
    @7
    cc0
    @2
    cle
    wbr
    #
    w3a
    #
    cc0
    cA
    @2
    crmx
    co
    clt
    wbr
    #
    cc0
    @3
    cle
    wbr
    #
    @9
    @1
    @2
    cn0
    wcel
    #
    @10
    @11
    wa
    @1
    @7
    @8
    simp1
    @7
    @8
    @12
    @1
    @12
    @7
    @8
    wa
    @2
    elnn0z
    biimpri
    3adant1
    cA
    @2
    rmxypos
    syl2anc
    simprd
    cA
    @4
    rmyneg
    @2
    @4
    cA
    crmy
    oveq2
    @2
    @5
    cA
    crmy
    oveq2
    @2
    cB
    cA
    crmy
    oveq2
    @2
    @6
    cA
    crmy
    oveq2
    oddcomabszz
end
