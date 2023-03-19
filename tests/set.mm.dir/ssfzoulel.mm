include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "wo.mm"
include "cfzo.mm"
include "co.mm"
include "wss.mm"
include "wi.mm"
include "wa.mm"
include "wn.mm"
include "clt.mm"
include "simpl2.mm"
include "simpl3.mm"
include "wb.mm"
include "cr.mm"
include "zre.mm"
include "ltnle.mm"
include "syl2an.mm"
include "3adant1.mm"
include "biimpar.mm"
include "ssfzo12.mm"
include "syl3anc.mm"
include "adantl.mm"
include "0red.mm"
include "adantr.mm"
include "letr.mm"
include "expcomd.mm"
include "imp.mm"
include "con3d.mm"
include "ex.mm"
include "com23.mm"
include "nn0re.mm"
include "3anim123i.mm"
include "3coml.mm"
include "syl.mm"
include "expdimp.mm"
include "impancom.mm"
include "anim12d.mm"
include "ioran.mm"
include "ancom.mm"
include "bitri.mm"
include "syl6ibr.mm"
include "syld.mm"
include "con2d.mm"
include "con4d.mm"

theorem ssfzoulel
  let cA: class A
  let cB: class B
  let cN: class N


  assert |- ( ( N e. NN0 /\ A e. ZZ /\ B e. ZZ ) -> ( ( N <_ A \/ B <_ 0 ) -> ( ( A ..^ B ) C_ ( 0 ..^ N ) -> B <_ A ) ) )

  proof
    cN
    cn0
    wcel
    #
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    w3a
    #
    cN
    cA
    cle
    wbr
    #
    cB
    cc0
    cle
    wbr
    #
    wo
    #
    cA
    cB
    cfzo
    co
    cc0
    cN
    cfzo
    co
    wss
    #
    cB
    cA
    cle
    wbr
    #
    wi
    @3
    @6
    wa
    @8
    @7
    @3
    @8
    wn
    #
    @6
    @7
    wn
    @3
    @9
    wa
    #
    @7
    @6
    @10
    @7
    cc0
    cA
    cle
    wbr
    #
    cB
    cN
    cle
    wbr
    #
    wa
    #
    @6
    wn
    #
    @10
    @1
    @2
    cA
    cB
    clt
    wbr
    #
    @7
    @13
    wi
    @0
    @1
    @2
    @9
    simpl2
    @0
    @1
    @2
    @9
    simpl3
    @3
    @15
    @9
    @1
    @2
    @15
    @9
    wb
    #
    @0
    @1
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @16
    @2
    cA
    zre
    #
    cB
    zre
    #
    cA
    cB
    ltnle
    syl2an
    3adant1
    biimpar
    cA
    cB
    cc0
    cN
    ssfzo12
    syl3anc
    @10
    @13
    @5
    wn
    #
    @4
    wn
    #
    wa
    #
    @14
    @10
    @11
    @21
    @12
    @22
    @3
    @9
    @11
    @21
    wi
    @3
    @11
    @9
    @21
    @1
    @2
    @11
    @9
    @21
    wi
    #
    wi
    @0
    @1
    @2
    wa
    #
    @11
    @24
    @25
    @11
    wa
    @5
    @8
    @25
    @11
    @5
    @8
    wi
    @25
    @5
    @11
    @8
    @25
    @18
    cc0
    cr
    wcel
    @17
    @5
    @11
    wa
    @8
    wi
    @2
    @18
    @1
    @20
    adantl
    @25
    0red
    @1
    @17
    @2
    @19
    adantr
    cB
    cc0
    cA
    letr
    syl3anc
    expcomd
    imp
    con3d
    ex
    3adant1
    com23
    imp
    @3
    @12
    @9
    @22
    @3
    @12
    wa
    @4
    @8
    @3
    @12
    @4
    @8
    @3
    @18
    cN
    cr
    wcel
    #
    @17
    w3a
    #
    @12
    @4
    wa
    @8
    wi
    @2
    @0
    @1
    @27
    @2
    @18
    @0
    @26
    @1
    @17
    @20
    cN
    nn0re
    @19
    3anim123i
    3coml
    cB
    cN
    cA
    letr
    syl
    expdimp
    con3d
    impancom
    anim12d
    @14
    @22
    @21
    wa
    @23
    @4
    @5
    ioran
    @22
    @21
    ancom
    bitri
    syl6ibr
    syld
    con2d
    impancom
    con4d
    ex
end
