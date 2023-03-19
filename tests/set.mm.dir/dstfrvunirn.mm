include "cdm.mm"
include "cuni.mm"
include "cn.mm"
include "cv.mm"
include "cle.mm"
include "corvc.mm"
include "co.mm"
include "ciun.mm"
include "cmpt.mm"
include "crn.mm"
include "wcel.mm"
include "wrex.mm"
include "wa.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "cfl.mm"
include "caddc.mm"
include "cr.mm"
include "1red.mm"
include "rrvvf.mm"
include "ffvelrnda.mm"
include "ifcld.mm"
include "breq2.mm"
include "1le1.mm"
include "a1i.mm"
include "wn.mm"
include "lenltd.mm"
include "biimpar.mm"
include "ifbothda.mm"
include "flge1nn.mm"
include "syl2anc.mm"
include "peano2nnd.mm"
include "cprb.mm"
include "adantr.mm"
include "crrv.mm"
include "nnred.mm"
include "simpr.mm"
include "ltled.mm"
include "leidd.mm"
include "fllep1.mm"
include "syl.mm"
include "letrd.mm"
include "dstfrvel.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "ex.mm"
include "wi.mm"
include "orvclteel.mm"
include "elunii.mm"
include "expcom.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "eliun.mm"
include "syl6bbr.mm"
include "eqrdv.mm"
include "ovex.mm"
include "dfiun3.mm"
include "syl6req.mm"

theorem dstfrvunirn
  let wph: wff ph
  let cP: class P
  let vn: setvar n
  let cX: class X
  let vx: setvar x
  assume dstfrv.1: |- ( ph -> P e. Prob )
  assume dstfrv.2: |- ( ph -> X e. ( rRndVar ` P ) )

  disjoint P n
  disjoint X n
  disjoint n ph
  disjoint n x
  disjoint P x
  disjoint X x
  disjoint ph x
  assert |- ( ph -> U. ran ( n e. NN |-> ( X oRVC <_ n ) ) = U. dom P )

  proof
    wph
    cP
    cdm
    #
    cuni
    #
    vn
    cn
    cX
    vn
    cv
    #
    cle
    corvc
    #
    co
    #
    ciun
    #
    vn
    cn
    @4
    cmpt
    crn
    cuni
    wph
    vx
    @1
    @5
    wph
    vx
    cv
    #
    @1
    wcel
    #
    @6
    @4
    wcel
    #
    vn
    cn
    wrex
    #
    @6
    @5
    wcel
    wph
    @7
    @9
    wph
    @7
    @9
    wph
    @7
    wa
    #
    @6
    cX
    cfv
    #
    c1
    clt
    wbr
    #
    c1
    @11
    cif
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cn
    wcel
    @6
    cX
    @15
    @3
    co
    #
    wcel
    #
    @9
    @10
    @14
    @10
    @13
    cr
    wcel
    #
    c1
    @13
    cle
    wbr
    #
    @14
    cn
    wcel
    @10
    @12
    c1
    @11
    cr
    @10
    1red
    #
    wph
    @1
    cr
    @6
    cX
    wph
    cP
    cX
    dstfrv.1
    dstfrv.2
    rrvvf
    ffvelrnda
    #
    ifcld
    #
    @12
    c1
    c1
    cle
    wbr
    #
    c1
    @11
    cle
    wbr
    #
    @19
    @10
    c1
    @11
    c1
    @13
    c1
    cle
    breq2
    @11
    @13
    c1
    cle
    breq2
    @23
    @10
    @12
    wa
    #
    1le1
    a1i
    @10
    @24
    @12
    wn
    #
    @10
    c1
    @11
    @20
    @21
    lenltd
    biimpar
    ifbothda
    @13
    flge1nn
    syl2anc
    peano2nnd
    #
    @10
    @15
    @6
    cP
    cX
    wph
    cP
    cprb
    wcel
    #
    @7
    dstfrv.1
    adantr
    wph
    cX
    cP
    crrv
    cfv
    wcel
    #
    @7
    dstfrv.2
    adantr
    @10
    @15
    @27
    nnred
    #
    wph
    @7
    simpr
    @10
    @11
    @13
    @15
    @21
    @22
    @30
    @12
    @11
    c1
    cle
    wbr
    @11
    @11
    cle
    wbr
    #
    @11
    @13
    cle
    wbr
    @10
    c1
    @11
    c1
    @13
    @11
    cle
    breq2
    @11
    @13
    @11
    cle
    breq2
    @25
    @11
    c1
    @10
    @11
    cr
    wcel
    @12
    @21
    adantr
    @25
    1red
    @10
    @12
    simpr
    ltled
    @10
    @31
    @26
    @10
    @11
    @21
    leidd
    adantr
    ifbothda
    @10
    @18
    @13
    @15
    cle
    wbr
    @22
    @13
    fllep1
    syl
    letrd
    dstfrvel
    @8
    @17
    vn
    @15
    cn
    @2
    @15
    wceq
    @4
    @16
    @6
    @2
    @15
    cX
    @3
    oveq2
    eleq2d
    rspcev
    syl2anc
    ex
    wph
    @8
    @7
    vn
    cn
    wph
    @2
    cn
    wcel
    #
    wa
    #
    @4
    @0
    wcel
    #
    @8
    @7
    wi
    @33
    @2
    cP
    cX
    wph
    @28
    @32
    dstfrv.1
    adantr
    wph
    @29
    @32
    dstfrv.2
    adantr
    @33
    @2
    wph
    @32
    simpr
    nnred
    orvclteel
    @8
    @34
    @7
    @6
    @4
    @0
    elunii
    expcom
    syl
    rexlimdva
    impbid
    vn
    @6
    cn
    @4
    eliun
    syl6bbr
    eqrdv
    vn
    cn
    @4
    cX
    @2
    @3
    ovex
    dfiun3
    syl6req
end
