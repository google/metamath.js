include "ccrcts.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "crctcshlem4.mm"
include "wi.mm"
include "breq12.mm"
include "syl5ibrcom.mm"
include "adantr.mm"
include "mpd.mm"
include "wne.mm"
include "ctrls.mm"
include "chash.mm"
include "crctcshtrl.mm"
include "caddc.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "cle.mm"
include "cif.mm"
include "cfz.mm"
include "cvv.mm"
include "cmpt.mm"
include "a1i.mm"
include "breq1.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "ifbieq12d.mm"
include "cfzo.mm"
include "wcel.mm"
include "elfzo0le.mm"
include "syl.mm"
include "crctcshlem1.mm"
include "nn0red.mm"
include "cz.mm"
include "elfzoelz.mm"
include "zred.mm"
include "subge0d.mm"
include "mpbird.mm"
include "iftrued.mm"
include "sylan9eqr.mm"
include "cn0.mm"
include "0elfz.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "wn.mm"
include "clt.mm"
include "elfzoel2.mm"
include "elfzonn0.mm"
include "cn.mm"
include "simpr.mm"
include "anim1i.mm"
include "elnnne0.mm"
include "sylibr.mm"
include "nngt0d.mm"
include "cr.mm"
include "wb.mm"
include "zre.mm"
include "nn0re.mm"
include "anim12ci.mm"
include "ltsubpos.mm"
include "bicomd.mm"
include "ex.mm"
include "syl2anc.mm"
include "imp.mm"
include "crctcshlem2.mm"
include "breq1d.mm"
include "notbid.mm"
include "resubcld.mm"
include "jca.mm"
include "ltnle.mm"
include "bitr4d.mm"
include "iffalsed.mm"
include "eqeltrd.mm"
include "nn0cnd.mm"
include "zcnd.mm"
include "addsubd.mm"
include "subidd.mm"
include "eqtrd.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "eqtr4d.mm"
include "iscrct.mm"
include "sylanbrc.mm"
include "pm2.61dane.mm"

theorem crctcsh
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  assume crctcsh.v: |- V = ( Vtx ` G )
  assume crctcsh.i: |- I = ( iEdg ` G )
  assume crctcsh.d: |- ( ph -> F ( Circuits ` G ) P )
  assume crctcsh.n: |- N = ( # ` F )
  assume crctcsh.s: |- ( ph -> S e. ( 0 ..^ N ) )
  assume crctcsh.h: |- H = ( F cyclShift S )
  assume crctcsh.q: |- Q = ( x e. ( 0 ... N ) |-> if ( x <_ ( N - S ) , ( P ` ( x + S ) ) , ( P ` ( ( x + S ) - N ) ) ) )

  disjoint N x
  disjoint P x
  disjoint S x
  disjoint ph x
  disjoint F x
  disjoint I x
  disjoint V x
  disjoint H x
  disjoint F i
  disjoint F j
  disjoint F k
  disjoint i j
  disjoint i k
  disjoint i x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint G i
  disjoint G j
  disjoint H j
  disjoint I i
  disjoint I j
  disjoint I k
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint P i
  disjoint P j
  disjoint P k
  disjoint Q j
  disjoint S i
  disjoint S j
  disjoint S k
  disjoint V i
  disjoint V j
  disjoint V k
  disjoint i ph
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> H ( Circuits ` G ) Q )

  proof
    wph
    cH
    cQ
    cG
    ccrcts
    cfv
    #
    wbr
    #
    cS
    cc0
    wph
    cS
    cc0
    wceq
    #
    wa
    cH
    cF
    wceq
    cQ
    cP
    wceq
    wa
    #
    @1
    wph
    vx
    cP
    cQ
    cS
    cF
    cG
    cH
    cI
    cN
    cV
    crctcsh.v
    crctcsh.i
    crctcsh.d
    crctcsh.n
    crctcsh.s
    crctcsh.h
    crctcsh.q
    crctcshlem4
    wph
    @3
    @1
    wi
    @2
    wph
    @1
    @3
    cF
    cP
    @0
    wbr
    #
    crctcsh.d
    cH
    cF
    cQ
    cP
    @0
    breq12
    syl5ibrcom
    adantr
    mpd
    wph
    cS
    cc0
    wne
    #
    wa
    #
    cH
    cQ
    cG
    ctrls
    cfv
    wbr
    #
    cc0
    cQ
    cfv
    #
    cH
    chash
    cfv
    #
    cQ
    cfv
    #
    wceq
    @1
    wph
    @7
    @5
    wph
    vx
    cP
    cQ
    cS
    cF
    cG
    cH
    cI
    cN
    cV
    crctcsh.v
    crctcsh.i
    crctcsh.d
    crctcsh.n
    crctcsh.s
    crctcsh.h
    crctcsh.q
    crctcshtrl
    adantr
    @6
    @8
    cc0
    cS
    caddc
    co
    #
    cP
    cfv
    #
    @10
    @6
    vx
    cc0
    vx
    cv
    #
    cN
    cS
    cmin
    co
    #
    cle
    wbr
    #
    @13
    cS
    caddc
    co
    #
    cP
    cfv
    #
    @16
    cN
    cmin
    co
    #
    cP
    cfv
    #
    cif
    #
    @12
    cc0
    cN
    cfz
    co
    #
    cQ
    cvv
    cQ
    vx
    @21
    @20
    cmpt
    wceq
    @6
    crctcsh.q
    a1i
    #
    @13
    cc0
    wceq
    #
    @6
    @20
    cc0
    @14
    cle
    wbr
    #
    @12
    @11
    cN
    cmin
    co
    #
    cP
    cfv
    #
    cif
    @12
    @23
    @15
    @24
    @17
    @19
    @12
    @26
    @13
    cc0
    @14
    cle
    breq1
    @23
    @16
    @11
    cP
    @13
    cc0
    cS
    caddc
    oveq1
    #
    fveq2d
    @23
    @18
    @25
    cP
    @23
    @16
    @11
    cN
    cmin
    @27
    oveq1d
    fveq2d
    ifbieq12d
    @6
    @24
    @12
    @26
    wph
    @24
    @5
    wph
    @24
    cS
    cN
    cle
    wbr
    #
    wph
    cS
    cc0
    cN
    cfzo
    co
    wcel
    #
    @28
    crctcsh.s
    cS
    cN
    elfzo0le
    syl
    wph
    cN
    cS
    wph
    cN
    wph
    cP
    cF
    cG
    cI
    cN
    cV
    crctcsh.v
    crctcsh.i
    crctcsh.d
    crctcsh.n
    crctcshlem1
    #
    nn0red
    #
    wph
    cS
    wph
    @29
    cS
    cz
    wcel
    crctcsh.s
    cS
    cc0
    cN
    elfzoelz
    syl
    #
    zred
    #
    subge0d
    mpbird
    adantr
    iftrued
    sylan9eqr
    @6
    cN
    cn0
    wcel
    #
    cc0
    @21
    wcel
    @6
    cP
    cF
    cG
    cI
    cN
    cV
    crctcsh.v
    crctcsh.i
    wph
    @4
    @5
    crctcsh.d
    adantr
    #
    crctcsh.n
    crctcshlem1
    cN
    0elfz
    syl
    @6
    @11
    cP
    fvexd
    #
    fvmptd
    @6
    vx
    @9
    @20
    @12
    @21
    cQ
    cvv
    @22
    @6
    @13
    @9
    wceq
    #
    wa
    @20
    @9
    cS
    caddc
    co
    #
    cN
    cmin
    co
    #
    cP
    cfv
    #
    @12
    @37
    @6
    @20
    @9
    @14
    cle
    wbr
    #
    @38
    cP
    cfv
    #
    @40
    cif
    @40
    @37
    @15
    @41
    @17
    @19
    @42
    @40
    @13
    @9
    @14
    cle
    breq1
    @37
    @16
    @38
    cP
    @13
    @9
    cS
    caddc
    oveq1
    #
    fveq2d
    @37
    @18
    @39
    cP
    @37
    @16
    @38
    cN
    cmin
    @43
    oveq1d
    fveq2d
    ifbieq12d
    @6
    @41
    @42
    @40
    @6
    @41
    wn
    #
    @14
    cN
    clt
    wbr
    #
    wph
    @5
    @45
    wph
    @29
    @5
    @45
    wi
    #
    crctcsh.s
    @29
    cN
    cz
    wcel
    #
    cS
    cn0
    wcel
    #
    @46
    cS
    cc0
    cN
    elfzoel2
    cS
    cN
    elfzonn0
    @47
    @48
    wa
    #
    @5
    @45
    @49
    @5
    wa
    #
    @45
    cc0
    cS
    clt
    wbr
    #
    @50
    cS
    @50
    @48
    @5
    wa
    cS
    cn
    wcel
    @49
    @48
    @5
    @47
    @48
    simpr
    anim1i
    cS
    elnnne0
    sylibr
    nngt0d
    @50
    cS
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    wa
    #
    @45
    @51
    wb
    @49
    @54
    @5
    @47
    @53
    @48
    @52
    cN
    zre
    cS
    nn0re
    anim12ci
    adantr
    @54
    @51
    @45
    cS
    cN
    ltsubpos
    bicomd
    syl
    mpbird
    ex
    syl2anc
    syl
    imp
    @6
    @44
    cN
    @14
    cle
    wbr
    #
    wn
    #
    @45
    @6
    @41
    @55
    @6
    @9
    cN
    @14
    cle
    @6
    cP
    cS
    cF
    cG
    cH
    cI
    cN
    cV
    crctcsh.v
    crctcsh.i
    @35
    crctcsh.n
    wph
    @29
    @5
    crctcsh.s
    adantr
    crctcsh.h
    crctcshlem2
    breq1d
    notbid
    @6
    @14
    cr
    wcel
    #
    @53
    wa
    #
    @45
    @56
    wb
    wph
    @58
    @5
    wph
    @57
    @53
    wph
    cN
    cS
    @31
    @33
    resubcld
    @31
    jca
    adantr
    @14
    cN
    ltnle
    syl
    bitr4d
    mpbird
    iffalsed
    sylan9eqr
    @6
    @40
    @12
    wceq
    #
    @37
    wph
    @59
    @5
    wph
    @39
    @11
    cP
    wph
    @39
    @9
    cN
    cmin
    co
    #
    cS
    caddc
    co
    @11
    wph
    @9
    cS
    cN
    wph
    @9
    wph
    @9
    cN
    cn0
    wph
    cP
    cS
    cF
    cG
    cH
    cI
    cN
    cV
    crctcsh.v
    crctcsh.i
    crctcsh.d
    crctcsh.n
    crctcsh.s
    crctcsh.h
    crctcshlem2
    #
    @30
    eqeltrd
    nn0cnd
    wph
    cS
    @32
    zcnd
    wph
    cN
    @30
    nn0cnd
    #
    addsubd
    wph
    @60
    cc0
    cS
    caddc
    wph
    @60
    cN
    cN
    cmin
    co
    cc0
    wph
    @9
    cN
    cN
    cmin
    @61
    oveq1d
    wph
    cN
    @62
    subidd
    eqtrd
    oveq1d
    eqtrd
    fveq2d
    adantr
    adantr
    eqtrd
    @6
    @9
    cN
    @21
    wph
    @9
    cN
    wceq
    @5
    @61
    adantr
    wph
    cN
    @21
    wcel
    #
    @5
    wph
    @34
    @63
    @30
    cN
    nn0fz0
    sylib
    adantr
    eqeltrd
    @36
    fvmptd
    eqtr4d
    cQ
    cH
    cG
    iscrct
    sylanbrc
    pm2.61dane
end
