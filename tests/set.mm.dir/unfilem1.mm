include "crn.mm"
include "coa.mm"
include "co.mm"
include "cdif.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "com.mm"
include "wb.mm"
include "elnn.mm"
include "mpan2.mm"
include "nnaord.mm"
include "mp3an23.mm"
include "syl.mm"
include "ibi.mm"
include "wss.mm"
include "nnaword1.mm"
include "word.mm"
include "nnord.mm"
include "ax-mp.mm"
include "nnacl.mm"
include "ordtri1.mm"
include "sylancr.mm"
include "mpbid.mm"
include "jca.mm"
include "eleq1.mm"
include "notbid.mm"
include "anbi12d.mm"
include "biimparc.mm"
include "sylan.mm"
include "rexlimiva.mm"
include "nnacli.mm"
include "syl2an.mm"
include "nnawordex.mm"
include "bitr3d.mm"
include "sylan9bb.mm"
include "biimprcd.mm"
include "wi.mm"
include "eqcom.mm"
include "biimpi.mm"
include "adantl.mm"
include "a1i.mm"
include "jcad.mm"
include "reximdv2.mm"
include "sylbid.mm"
include "imp.mm"
include "impbii.mm"
include "ovex.mm"
include "elrnmpti.mm"
include "eldif.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem unfilem1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  assume unfilem1.1: |- A e. _om
  assume unfilem1.2: |- B e. _om
  assume unfilem1.3: |- F = ( x e. B |-> ( A +o x ) )

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint F w
  disjoint F y
  disjoint F z
  assert |- ran F = ( ( A +o B ) \ A )

  proof
    vy
    cF
    crn
    #
    cA
    cB
    coa
    co
    #
    cA
    cdif
    #
    vy
    cv
    #
    cA
    vx
    cv
    #
    coa
    co
    #
    wceq
    #
    vx
    cB
    wrex
    #
    @3
    @1
    wcel
    #
    @3
    cA
    wcel
    #
    wn
    #
    wa
    #
    @3
    @0
    wcel
    @3
    @2
    wcel
    @7
    @11
    @6
    @11
    vx
    cB
    @4
    cB
    wcel
    #
    @5
    @1
    wcel
    #
    @5
    cA
    wcel
    #
    wn
    #
    wa
    #
    @6
    @11
    @12
    @13
    @15
    @12
    @13
    @12
    @4
    com
    wcel
    #
    @12
    @13
    wb
    #
    @12
    cB
    com
    wcel
    #
    @17
    unfilem1.2
    @4
    cB
    elnn
    mpan2
    #
    @17
    @19
    cA
    com
    wcel
    #
    @18
    unfilem1.2
    unfilem1.1
    @4
    cB
    cA
    nnaord
    mp3an23
    #
    syl
    ibi
    @12
    @21
    @17
    @15
    unfilem1.1
    @20
    @21
    @17
    wa
    #
    cA
    @5
    wss
    #
    @15
    cA
    @4
    nnaword1
    @23
    cA
    word
    #
    @5
    word
    #
    @24
    @15
    wb
    @21
    @25
    unfilem1.1
    cA
    nnord
    #
    ax-mp
    @23
    @5
    com
    wcel
    @26
    cA
    @4
    nnacl
    @5
    nnord
    syl
    cA
    @5
    ordtri1
    sylancr
    mpbid
    sylancr
    jca
    @6
    @11
    @16
    @6
    @8
    @13
    @10
    @15
    @3
    @5
    @1
    eleq1
    @6
    @9
    @14
    @3
    @5
    cA
    eleq1
    notbid
    anbi12d
    biimparc
    sylan
    rexlimiva
    @8
    @10
    @7
    @8
    @10
    @5
    @3
    wceq
    #
    vx
    com
    wrex
    #
    @7
    @8
    @21
    @3
    com
    wcel
    #
    @10
    @29
    wb
    unfilem1.1
    @8
    @1
    com
    wcel
    @30
    cA
    cB
    unfilem1.1
    unfilem1.2
    nnacli
    @3
    @1
    elnn
    mpan2
    @21
    @30
    wa
    cA
    @3
    wss
    #
    @10
    @29
    @21
    @25
    @3
    word
    @31
    @10
    wb
    @30
    @27
    @3
    nnord
    cA
    @3
    ordtri1
    syl2an
    vx
    cA
    @3
    nnawordex
    bitr3d
    sylancr
    @8
    @28
    @6
    vx
    com
    cB
    @8
    @17
    @28
    wa
    #
    @12
    @6
    @32
    @12
    @8
    @17
    @12
    @13
    @28
    @8
    @22
    @5
    @3
    @1
    eleq1
    sylan9bb
    biimprcd
    @32
    @6
    wi
    @8
    @28
    @6
    @17
    @28
    @6
    @5
    @3
    eqcom
    biimpi
    adantl
    a1i
    jcad
    reximdv2
    sylbid
    imp
    impbii
    vx
    cB
    @5
    @3
    cF
    unfilem1.3
    cA
    @4
    coa
    ovex
    elrnmpti
    @3
    @1
    cA
    eldif
    3bitr4i
    eqriv
end
