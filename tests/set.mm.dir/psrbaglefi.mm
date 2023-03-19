include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "crab.mm"
include "cc0.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cixp.mm"
include "cfn.mm"
include "cab.mm"
include "df-rab.mm"
include "cn0.mm"
include "wf.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "wb.mm"
include "psrbag.mm"
include "adantr.mm"
include "simpl.mm"
include "syl6bi.mm"
include "adantrd.mm"
include "wi.mm"
include "wss.mm"
include "ss2ixp.mm"
include "fz0ssnn0.mm"
include "a1i.mm"
include "mprg.mm"
include "sseli.mm"
include "vex.mm"
include "elixpconst.mm"
include "sylib.mm"
include "wral.mm"
include "wfn.mm"
include "ffn.mm"
include "adantl.mm"
include "elixp.mm"
include "baib.mm"
include "syl.mm"
include "cuz.mm"
include "cz.mm"
include "ffvelrn.mm"
include "adantll.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "psrbagf.mm"
include "ffvelrnda.mm"
include "nn0zd.mm"
include "elfz5.mm"
include "syl2anc.mm"
include "ralbidva.mm"
include "ffnd.mm"
include "simpll.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofrfval.mm"
include "bitr4d.mm"
include "psrbaglecl.mm"
include "3exp2.mm"
include "imp31.mm"
include "pm4.71rd.mm"
include "3bitrrd.mm"
include "ex.mm"
include "pm5.21ndd.mm"
include "abbi1dv.mm"
include "syl5eq.mm"
include "cmap.mm"
include "simpr.mm"
include "wceq.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "eleq1d.mm"
include "elrab2.mm"
include "simprd.mm"
include "fzfid.mm"
include "cdif.mm"
include "csn.mm"
include "cvv.mm"
include "csupp.mm"
include "jca.mm"
include "frnnn0supp.mm"
include "eqimss.mm"
include "3syl.mm"
include "c0ex.mm"
include "suppssr.mm"
include "oveq2d.mm"
include "fz0sn.mm"
include "syl6eq.mm"
include "ixpfi2.mm"
include "eqeltrd.mm"

theorem psrbaglefi
  let vy: setvar y
  let cD: class D
  let vf: setvar f
  let cF: class F
  let cI: class I
  let cV: class V
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z
  let cG: class G
  let wph: wff ph
  let cS: class S
  let cB: class B
  let cX: class X
  let cY: class Y
  assume psrbag.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }

  disjoint f y
  disjoint F f
  disjoint F y
  disjoint V y
  disjoint I f
  disjoint I y
  disjoint D y
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f z
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k n
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F z
  disjoint G f
  disjoint G j
  disjoint G k
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint V m
  disjoint V n
  disjoint V x
  disjoint V z
  disjoint I m
  disjoint I n
  disjoint I w
  disjoint I x
  disjoint I z
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph z
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S z
  disjoint B j
  disjoint B k
  disjoint B m
  disjoint D j
  disjoint D k
  disjoint D m
  disjoint D n
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D x
  disjoint D z
  disjoint X f
  disjoint X m
  disjoint X n
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y f
  disjoint Y k
  disjoint Y m
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  assert |- ( ( I e. V /\ F e. D ) -> { y e. D | y oR <_ F } e. Fin )

  proof
    cI
    cV
    wcel
    #
    cF
    cD
    wcel
    #
    wa
    #
    vy
    cv
    #
    cF
    cle
    cofr
    wbr
    #
    vy
    cD
    crab
    #
    vx
    cI
    cc0
    vx
    cv
    #
    cF
    cfv
    #
    cfz
    co
    #
    cixp
    #
    cfn
    @2
    @5
    @3
    cD
    wcel
    #
    @4
    wa
    #
    vy
    cab
    @9
    @4
    vy
    cD
    df-rab
    @2
    @11
    vy
    @9
    @2
    cI
    cn0
    @3
    wf
    #
    @11
    @3
    @9
    wcel
    #
    @2
    @10
    @12
    @4
    @2
    @10
    @12
    @3
    ccnv
    cn
    cima
    cfn
    wcel
    #
    wa
    #
    @12
    @0
    @10
    @15
    wb
    @1
    cD
    vf
    @3
    cI
    cV
    psrbag.d
    psrbag
    adantr
    @12
    @14
    simpl
    syl6bi
    adantrd
    @13
    @12
    wi
    @2
    @13
    @3
    vx
    cI
    cn0
    cixp
    #
    wcel
    @12
    @9
    @16
    @3
    @8
    cn0
    wss
    #
    @9
    @16
    wss
    vx
    cI
    vx
    cI
    @8
    cn0
    ss2ixp
    @17
    @6
    cI
    wcel
    #
    @7
    fz0ssnn0
    a1i
    mprg
    sseli
    vx
    cI
    cn0
    @3
    vy
    vex
    #
    elixpconst
    sylib
    a1i
    @2
    @12
    @11
    @13
    wb
    @2
    @12
    wa
    #
    @13
    @6
    @3
    cfv
    #
    @8
    wcel
    #
    vx
    cI
    wral
    #
    @4
    @11
    @20
    @3
    cI
    wfn
    #
    @13
    @23
    wb
    @12
    @24
    @2
    cI
    cn0
    @3
    ffn
    adantl
    #
    @13
    @24
    @23
    vx
    cI
    @8
    @3
    @19
    elixp
    baib
    syl
    @20
    @23
    @21
    @7
    cle
    wbr
    #
    vx
    cI
    wral
    @4
    @20
    @22
    @26
    vx
    cI
    @20
    @18
    wa
    #
    @21
    cc0
    cuz
    cfv
    #
    wcel
    @7
    cz
    wcel
    @22
    @26
    wb
    @27
    @21
    cn0
    @28
    @12
    @18
    @21
    cn0
    wcel
    @2
    cI
    cn0
    @6
    @3
    ffvelrn
    adantll
    nn0uz
    syl6eleq
    @27
    @7
    @20
    cI
    cn0
    @6
    cF
    @2
    cI
    cn0
    cF
    wf
    #
    @12
    cD
    vf
    cF
    cI
    cV
    psrbag.d
    psrbagf
    #
    adantr
    #
    ffvelrnda
    nn0zd
    @21
    cc0
    @7
    elfz5
    syl2anc
    ralbidva
    @20
    vx
    cI
    cI
    @21
    @7
    cle
    cI
    @3
    cF
    cV
    cV
    @25
    @20
    cI
    cn0
    cF
    @31
    ffnd
    @0
    @1
    @12
    simpll
    #
    @32
    cI
    inidm
    @27
    @21
    eqidd
    @27
    @7
    eqidd
    ofrfval
    bitr4d
    @20
    @4
    @10
    @0
    @1
    @12
    @4
    @10
    wi
    @0
    @1
    @12
    @4
    @10
    cD
    vf
    cF
    @3
    cI
    cV
    psrbag.d
    psrbaglecl
    3exp2
    imp31
    pm4.71rd
    3bitrrd
    ex
    pm5.21ndd
    abbi1dv
    syl5eq
    @2
    vx
    cI
    @8
    cF
    ccnv
    #
    cn
    cima
    #
    cc0
    @2
    cF
    cn0
    cI
    cmap
    co
    #
    wcel
    #
    @34
    cfn
    wcel
    #
    @2
    @1
    @36
    @37
    wa
    @0
    @1
    simpr
    vf
    cv
    #
    ccnv
    #
    cn
    cima
    #
    cfn
    wcel
    @37
    vf
    cF
    @35
    cD
    @38
    cF
    wceq
    #
    @40
    @34
    cfn
    @41
    @39
    @33
    cn
    @38
    cF
    cnveq
    imaeq1d
    eleq1d
    psrbag.d
    elrab2
    sylib
    simprd
    @2
    @18
    wa
    cc0
    @7
    fzfid
    @2
    @6
    cI
    @34
    cdif
    wcel
    wa
    #
    @8
    cc0
    csn
    #
    wceq
    @8
    @43
    wss
    @42
    @8
    cc0
    cc0
    cfz
    co
    @43
    @42
    @7
    cc0
    cc0
    cfz
    @2
    cI
    cn0
    cvv
    cF
    cV
    @34
    @6
    cc0
    @30
    @2
    @0
    @29
    wa
    cF
    cc0
    csupp
    co
    #
    @34
    wceq
    @44
    @34
    wss
    @2
    @0
    @29
    @0
    @1
    simpl
    #
    @30
    jca
    cF
    cI
    cV
    frnnn0supp
    @44
    @34
    eqimss
    3syl
    @45
    cc0
    cvv
    wcel
    @2
    c0ex
    a1i
    suppssr
    oveq2d
    fz0sn
    syl6eq
    @8
    @43
    eqimss
    syl
    ixpfi2
    eqeltrd
end
