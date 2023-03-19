include "con0.mm"
include "wss.mm"
include "cwdom.mm"
include "wbr.mm"
include "wa.mm"
include "cdm.mm"
include "wcel.mm"
include "cpw.mm"
include "cdom.mm"
include "char.mm"
include "cfv.mm"
include "word.mm"
include "cep.mm"
include "oicl.mm"
include "cvv.mm"
include "wb.mm"
include "cuni.mm"
include "csuc.mm"
include "relwdom.mm"
include "brrelexi.mm"
include "adantl.mm"
include "uniexg.mm"
include "sucexg.mm"
include "3syl.mm"
include "wf.mm"
include "wsmo.mm"
include "oif.mm"
include "onsucuni.mm"
include "adantr.mm"
include "fss.mm"
include "sylancr.mm"
include "crn.mm"
include "wceq.mm"
include "oismo.mm"
include "simpld.mm"
include "ssorduni.mm"
include "ordsuc.mm"
include "sylib.mm"
include "smorndom.mm"
include "syl3anc.mm"
include "ssexd.mm"
include "elong.mm"
include "syl.mm"
include "mpbiri.mm"
include "csdm.mm"
include "canth2g.mm"
include "sdomdom.mm"
include "cen.mm"
include "wf1o.mm"
include "wiso.mm"
include "wwe.mm"
include "wse.mm"
include "simpl.mm"
include "epweon.mm"
include "wess.mm"
include "mpisyl.mm"
include "epse.mm"
include "oiiso2.mm"
include "sylancl.mm"
include "isof1o.mm"
include "simprd.mm"
include "f1oeq3.mm"
include "mpbid.mm"
include "f1oen2g.mm"
include "endom.mm"
include "domwdom.mm"
include "wdomtr.mm"
include "sylancom.mm"
include "wdompwdom.mm"
include "domtr.mm"
include "syl2anc.mm"
include "elharval.mm"
include "sylanbrc.mm"

theorem hsmexlem1
  let cA: class A
  let cB: class B
  let cO: class O
  assume hsmexlem.o: |- O = OrdIso ( _E , A )


  assert |- ( ( A C_ On /\ A ~<_* B ) -> dom O e. ( har ` ~P B ) )

  proof
    cA
    con0
    wss
    #
    cA
    cB
    cwdom
    wbr
    #
    wa
    #
    cO
    cdm
    #
    con0
    wcel
    #
    @3
    cB
    cpw
    #
    cdom
    wbr
    #
    @3
    @5
    char
    cfv
    wcel
    @2
    @4
    @3
    word
    #
    cA
    cep
    cO
    hsmexlem.o
    oicl
    @2
    @3
    cvv
    wcel
    #
    @4
    @7
    wb
    @2
    @3
    cA
    cuni
    #
    csuc
    #
    cvv
    @2
    cA
    cvv
    wcel
    #
    @9
    cvv
    wcel
    @10
    cvv
    wcel
    @1
    @11
    @0
    cA
    cB
    cwdom
    relwdom
    brrelexi
    adantl
    #
    cA
    cvv
    uniexg
    @9
    cvv
    sucexg
    3syl
    @2
    @3
    @10
    cO
    wf
    #
    cO
    wsmo
    #
    @10
    word
    #
    @3
    @10
    wss
    @2
    @3
    cA
    cO
    wf
    cA
    @10
    wss
    #
    @13
    cA
    cep
    cO
    hsmexlem.o
    oif
    @0
    @16
    @1
    cA
    onsucuni
    adantr
    @3
    cA
    @10
    cO
    fss
    sylancr
    @2
    @14
    cO
    crn
    #
    cA
    wceq
    #
    @0
    @14
    @18
    wa
    @1
    cA
    cO
    hsmexlem.o
    oismo
    adantr
    #
    simpld
    @2
    @9
    word
    #
    @15
    @0
    @20
    @1
    cA
    ssorduni
    adantr
    @9
    ordsuc
    sylib
    @3
    @10
    cO
    smorndom
    syl3anc
    ssexd
    #
    @3
    cvv
    elong
    syl
    mpbiri
    #
    @2
    @3
    @3
    cpw
    #
    cdom
    wbr
    #
    @23
    @5
    cdom
    wbr
    #
    @6
    @2
    @8
    @3
    @23
    csdm
    wbr
    @24
    @21
    @3
    cvv
    canth2g
    @3
    @23
    sdomdom
    3syl
    @2
    @3
    cB
    cwdom
    wbr
    #
    @25
    @0
    @1
    @3
    cA
    cwdom
    wbr
    #
    @26
    @2
    @3
    cA
    cen
    wbr
    #
    @3
    cA
    cdom
    wbr
    @27
    @2
    @4
    @11
    @3
    cA
    cO
    wf1o
    #
    @28
    @22
    @12
    @2
    @3
    @17
    cO
    wf1o
    #
    @29
    @2
    @3
    @17
    cep
    cep
    cO
    wiso
    #
    @30
    @2
    cA
    cep
    wwe
    #
    cA
    cep
    wse
    @31
    @2
    @0
    con0
    cep
    wwe
    @32
    @0
    @1
    simpl
    epweon
    cA
    con0
    cep
    wess
    mpisyl
    cA
    epse
    cA
    cep
    cO
    hsmexlem.o
    oiiso2
    sylancl
    @3
    @17
    cep
    cep
    cO
    isof1o
    syl
    @2
    @18
    @30
    @29
    wb
    @2
    @14
    @18
    @19
    simprd
    @17
    cA
    @3
    cO
    f1oeq3
    syl
    mpbid
    @3
    cA
    cO
    con0
    cvv
    f1oen2g
    syl3anc
    @3
    cA
    endom
    @3
    cA
    domwdom
    3syl
    @3
    cA
    cB
    wdomtr
    sylancom
    @3
    cB
    wdompwdom
    syl
    @3
    @23
    @5
    domtr
    syl2anc
    @5
    @3
    elharval
    sylanbrc
end
