include "cabl.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "simpll.mm"
include "simplr.mm"
include "simprl.mm"
include "cle.mm"
include "cz.mm"
include "wss.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cn0.mm"
include "wf.mm"
include "odf.mm"
include "frn.mm"
include "ax-mp.mm"
include "nn0ssz.mm"
include "sstri.mm"
include "a1i.mm"
include "nnz.mm"
include "adantl.mm"
include "cdvds.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "adantr.mm"
include "gexod.mm"
include "sylan.mm"
include "wi.mm"
include "odcl.mm"
include "nn0zd.mm"
include "dvdsle.mm"
include "syl2anc.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "breq1.mm"
include "ralrn.mm"
include "sylibr.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "ad2antrr.mm"
include "fnfvelrn.mm"
include "suprzub.mm"
include "syl3anc.mm"
include "simplrr.mm"
include "breqtrrd.mm"
include "gexexlem.mm"
include "c0.mm"
include "wne.mm"
include "grpbn0.mm"
include "syl.mm"
include "cdm.mm"
include "fdmi.mm"
include "eqeq1i.mm"
include "dm0rn0.mm"
include "bitr3i.mm"
include "necon3bii.mm"
include "sylib.mm"
include "suprzcl2.mm"
include "fvelrnb.mm"
include "reximddv.mm"

theorem gexex
  let vx: setvar x
  let cE: class E
  let cG: class G
  let cO: class O
  let cX: class X
  let vp: setvar p
  let vy: setvar y
  let cA: class A
  let vn: setvar n
  let wph: wff ph
  assume gexex.1: |- X = ( Base ` G )
  assume gexex.2: |- E = ( gEx ` G )
  assume gexex.3: |- O = ( od ` G )

  disjoint E x
  disjoint G x
  disjoint O x
  disjoint X x
  disjoint p x
  disjoint p y
  disjoint A p
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint n x
  disjoint n y
  disjoint E n
  disjoint E y
  disjoint G y
  disjoint n p
  disjoint O n
  disjoint O p
  disjoint O y
  disjoint p ph
  disjoint ph x
  disjoint ph y
  disjoint X p
  disjoint X y
  assert |- ( ( G e. Abel /\ E e. NN ) -> E. x e. X ( O ` x ) = E )

  proof
    cG
    cabl
    wcel
    #
    cE
    cn
    wcel
    #
    wa
    #
    vx
    cv
    #
    cO
    cfv
    #
    cO
    crn
    #
    cr
    clt
    csup
    #
    wceq
    #
    @4
    cE
    wceq
    vx
    cX
    @2
    @3
    cX
    wcel
    #
    @7
    wa
    #
    wa
    #
    vy
    @3
    cE
    cG
    cO
    cX
    gexex.1
    gexex.2
    gexex.3
    @0
    @1
    @9
    simpll
    @0
    @1
    @9
    simplr
    @2
    @8
    @7
    simprl
    @10
    vy
    cv
    #
    cX
    wcel
    #
    wa
    #
    @11
    cO
    cfv
    #
    @6
    @4
    cle
    @13
    @5
    cz
    wss
    #
    @11
    vn
    cv
    #
    cle
    wbr
    #
    vy
    @5
    wral
    #
    vn
    cz
    wrex
    #
    @14
    @5
    wcel
    #
    @14
    @6
    cle
    wbr
    @15
    @13
    @5
    cn0
    cz
    cX
    cn0
    cO
    wf
    #
    @5
    cn0
    wss
    cG
    cO
    cX
    gexex.1
    gexex.3
    odf
    #
    cX
    cn0
    cO
    frn
    ax-mp
    nn0ssz
    sstri
    #
    a1i
    @2
    @19
    @9
    @12
    @2
    cE
    cz
    wcel
    #
    @11
    cE
    cle
    wbr
    #
    vy
    @5
    wral
    #
    @19
    @1
    @24
    @0
    cE
    nnz
    adantl
    @2
    @4
    cE
    cle
    wbr
    #
    vx
    cX
    wral
    #
    @26
    @2
    @27
    vx
    cX
    @2
    @8
    wa
    #
    @4
    cE
    cdvds
    wbr
    #
    @27
    @2
    cG
    cgrp
    wcel
    #
    @8
    @30
    @0
    @31
    @1
    cG
    ablgrp
    adantr
    #
    @3
    cE
    cG
    cO
    cX
    gexex.1
    gexex.2
    gexex.3
    gexod
    sylan
    @29
    @4
    cz
    wcel
    @1
    @30
    @27
    wi
    @29
    @4
    @8
    @4
    cn0
    wcel
    @2
    @3
    cG
    cO
    cX
    gexex.1
    gexex.3
    odcl
    adantl
    nn0zd
    @0
    @1
    @8
    simplr
    @4
    cE
    dvdsle
    syl2anc
    mpd
    ralrimiva
    cO
    cX
    wfn
    #
    @26
    @28
    wb
    @21
    @33
    @22
    cX
    cn0
    cO
    ffn
    ax-mp
    #
    @25
    @27
    vy
    vx
    cX
    cO
    @11
    @4
    cE
    cle
    breq1
    ralrn
    ax-mp
    sylibr
    @18
    @26
    vn
    cE
    cz
    @16
    cE
    wceq
    @17
    @25
    vy
    @5
    @16
    cE
    @11
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    #
    ad2antrr
    @10
    @33
    @12
    @20
    @33
    @10
    @34
    a1i
    cX
    @11
    cO
    fnfvelrn
    sylan
    vn
    vy
    @5
    @14
    suprzub
    syl3anc
    @2
    @8
    @7
    @12
    simplrr
    breqtrrd
    gexexlem
    @2
    @6
    @5
    wcel
    #
    @7
    vx
    cX
    wrex
    #
    @2
    @15
    @5
    c0
    wne
    #
    @19
    @36
    @15
    @2
    @23
    a1i
    @2
    cX
    c0
    wne
    #
    @38
    @2
    @31
    @39
    @32
    cX
    cG
    gexex.1
    grpbn0
    syl
    cX
    c0
    @5
    c0
    cX
    c0
    wceq
    cO
    cdm
    #
    c0
    wceq
    @5
    c0
    wceq
    @40
    cX
    c0
    cX
    cn0
    cO
    @22
    fdmi
    eqeq1i
    cO
    dm0rn0
    bitr3i
    necon3bii
    sylib
    @35
    vn
    vy
    @5
    suprzcl2
    syl3anc
    @33
    @36
    @37
    wb
    @34
    vx
    cX
    @6
    cO
    fvelrnb
    ax-mp
    sylib
    reximddv
end
