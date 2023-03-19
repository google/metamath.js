include "clgs.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "c2.mm"
include "cdiv.mm"
include "cexp.mm"
include "caddc.mm"
include "cmo.mm"
include "cneg.mm"
include "cfz.mm"
include "cv.mm"
include "cmul.mm"
include "cfl.mm"
include "cfv.mm"
include "csu.mm"
include "cz.mm"
include "wcel.mm"
include "cprime.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "eldifad.mm"
include "prmz.mm"
include "syl.mm"
include "lgsval3.mm"
include "syl2anc.mm"
include "cr.mm"
include "crp.mm"
include "cn.mm"
include "prmnn.mm"
include "oddprm.mm"
include "nnnn0d.mm"
include "nnexpcld.mm"
include "nnred.mm"
include "neg1rr.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "neg1ne0.mm"
include "fzfid.mm"
include "wa.mm"
include "nndivred.mm"
include "adantr.mm"
include "2re.mm"
include "elfznn.mm"
include "adantl.mm"
include "remulcl.mm"
include "sylancr.mm"
include "remulcld.mm"
include "flcld.mm"
include "fsumzcl.mm"
include "reexpclzd.mm"
include "1re.mm"
include "nnrpd.mm"
include "czn.mm"
include "cmgp.mm"
include "czrh.mm"
include "cmpt.mm"
include "eqid.mm"
include "lgseisenlem4.mm"
include "modadd1.mm"
include "syl221anc.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "peano2re.mm"
include "df-neg.mm"
include "cabs.mm"
include "cc.mm"
include "neg1cn.mm"
include "absexpz.mm"
include "syl3anc.mm"
include "ax-1cn.mm"
include "absnegi.mm"
include "abs1.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "1exp.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "1le1.mm"
include "syl6eqbr.mm"
include "wb.mm"
include "absle.mm"
include "sylancl.mm"
include "mpbid.mm"
include "simpld.mm"
include "syl5eqbrr.mm"
include "0red.mm"
include "lesubaddd.mm"
include "peano2rem.mm"
include "simprd.mm"
include "df-2.mm"
include "eldifsni.mm"
include "cuz.mm"
include "prmuz2.mm"
include "eluzle.mm"
include "3syl.mm"
include "leltned.mm"
include "mpbird.mm"
include "ltaddsubd.mm"
include "lelttrd.mm"
include "modid.mm"
include "syl22anc.mm"
include "oveq1d.mm"
include "recnd.mm"
include "pncan.mm"

theorem lgseisen
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cQ: class Q
  let vk: setvar k
  let cG: class G
  let cL: class L
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  let cN: class N
  let cY: class Y
  let cR: class R
  let cS: class S
  assume lgseisen.1: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume lgseisen.2: |- ( ph -> Q e. ( Prime \ { 2 } ) )
  assume lgseisen.3: |- ( ph -> P =/= Q )

  disjoint P x
  disjoint ph x
  disjoint Q x
  disjoint k x
  disjoint G k
  disjoint G x
  disjoint L k
  disjoint L x
  disjoint k n
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint P k
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint P n
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint P u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint P v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint P w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint P y
  disjoint P z
  disjoint k ph
  disjoint n ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint M n
  disjoint M u
  disjoint M v
  disjoint M w
  disjoint M y
  disjoint M z
  disjoint N u
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint Q k
  disjoint Q u
  disjoint Q w
  disjoint Q y
  disjoint Q z
  disjoint Y k
  disjoint Y x
  disjoint R k
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S z
  assert |- ( ph -> ( Q /L P ) = ( -u 1 ^ sum_ x e. ( 1 ... ( ( P - 1 ) / 2 ) ) ( |_ ` ( ( Q / P ) x. ( 2 x. x ) ) ) ) )

  proof
    wph
    cQ
    cP
    clgs
    co
    #
    cQ
    cP
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    cP
    cmo
    co
    #
    c1
    cmin
    co
    #
    c1
    cneg
    #
    c1
    @2
    cfz
    co
    #
    cQ
    cP
    cdiv
    co
    #
    c2
    vx
    cv
    #
    cmul
    co
    #
    cmul
    co
    #
    cfl
    cfv
    #
    vx
    csu
    #
    cexp
    co
    #
    wph
    cQ
    cz
    wcel
    #
    cP
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    @0
    @5
    wceq
    wph
    cQ
    cprime
    wcel
    #
    @15
    wph
    cQ
    cprime
    @16
    lgseisen.2
    eldifad
    #
    cQ
    prmz
    syl
    lgseisen.1
    cQ
    cP
    lgsval3
    syl2anc
    wph
    @5
    @14
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    @14
    wph
    @4
    @20
    c1
    cmin
    wph
    @4
    @20
    cP
    cmo
    co
    #
    @20
    wph
    @3
    cr
    wcel
    @14
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    cP
    crp
    wcel
    #
    @3
    cP
    cmo
    co
    @14
    cP
    cmo
    co
    wceq
    @4
    @22
    wceq
    wph
    @3
    wph
    cQ
    @2
    wph
    @18
    cQ
    cn
    wcel
    @19
    cQ
    prmnn
    syl
    #
    wph
    @2
    wph
    @17
    @2
    cn
    wcel
    lgseisen.1
    cP
    oddprm
    syl
    nnnn0d
    nnexpcld
    nnred
    wph
    @6
    @13
    @6
    cr
    wcel
    wph
    neg1rr
    a1i
    @6
    cc0
    wne
    #
    wph
    neg1ne0
    a1i
    #
    wph
    @7
    @12
    vx
    wph
    c1
    @2
    fzfid
    wph
    @9
    @7
    wcel
    #
    wa
    #
    @11
    @30
    @8
    @10
    wph
    @8
    cr
    wcel
    @29
    wph
    cQ
    cP
    wph
    cQ
    @26
    nnred
    wph
    cP
    cprime
    wcel
    #
    cP
    cn
    wcel
    wph
    cP
    cprime
    @16
    lgseisen.1
    eldifad
    #
    cP
    prmnn
    syl
    #
    nndivred
    adantr
    @30
    c2
    cr
    wcel
    #
    @9
    cr
    wcel
    @10
    cr
    wcel
    2re
    @30
    @9
    @29
    @9
    cn
    wcel
    wph
    @9
    @2
    elfznn
    adantl
    nnred
    c2
    @9
    remulcl
    sylancr
    remulcld
    flcld
    fsumzcl
    #
    reexpclzd
    #
    @24
    wph
    1re
    a1i
    #
    wph
    cP
    @33
    nnrpd
    #
    wph
    vx
    vy
    cP
    cQ
    cQ
    @10
    cmul
    co
    cP
    cmo
    co
    #
    cQ
    c2
    vy
    cv
    cmul
    co
    cmul
    co
    cP
    cmo
    co
    #
    cP
    czn
    cfv
    #
    cmgp
    cfv
    #
    @41
    czrh
    cfv
    #
    vx
    @7
    @6
    @39
    cexp
    co
    @39
    cmul
    co
    cP
    cmo
    co
    c2
    cdiv
    co
    cmpt
    #
    @41
    lgseisen.1
    lgseisen.2
    lgseisen.3
    @39
    eqid
    @44
    eqid
    @40
    eqid
    @41
    eqid
    @42
    eqid
    @43
    eqid
    lgseisenlem4
    @3
    @14
    c1
    cP
    modadd1
    syl221anc
    wph
    @20
    cr
    wcel
    #
    @25
    cc0
    @20
    cle
    wbr
    #
    @20
    cP
    clt
    wbr
    #
    @22
    @20
    wceq
    wph
    @23
    @45
    @36
    @14
    peano2re
    syl
    @38
    wph
    cc0
    c1
    cmin
    co
    #
    @14
    cle
    wbr
    @46
    wph
    @48
    @6
    @14
    cle
    c1
    df-neg
    wph
    @6
    @14
    cle
    wbr
    #
    @14
    c1
    cle
    wbr
    #
    wph
    @14
    cabs
    cfv
    #
    c1
    cle
    wbr
    #
    @49
    @50
    wa
    #
    wph
    @51
    c1
    c1
    cle
    wph
    @51
    @6
    cabs
    cfv
    #
    @13
    cexp
    co
    #
    c1
    wph
    @6
    cc
    wcel
    #
    @27
    @13
    cz
    wcel
    #
    @51
    @55
    wceq
    @56
    wph
    neg1cn
    a1i
    @28
    @35
    @6
    @13
    absexpz
    syl3anc
    wph
    @55
    c1
    @13
    cexp
    co
    #
    c1
    @54
    c1
    @13
    cexp
    @54
    c1
    cabs
    cfv
    c1
    c1
    ax-1cn
    absnegi
    abs1
    eqtri
    oveq1i
    wph
    @57
    @58
    c1
    wceq
    @35
    @13
    1exp
    syl
    syl5eq
    eqtrd
    1le1
    syl6eqbr
    wph
    @23
    @24
    @52
    @53
    wb
    @36
    1re
    @14
    c1
    absle
    sylancl
    mpbid
    #
    simpld
    syl5eqbrr
    wph
    cc0
    c1
    @14
    wph
    0red
    @37
    @36
    lesubaddd
    mpbid
    wph
    @47
    @14
    @1
    clt
    wbr
    wph
    @14
    c1
    @1
    @36
    @37
    wph
    cP
    cr
    wcel
    @1
    cr
    wcel
    wph
    cP
    @33
    nnred
    #
    cP
    peano2rem
    syl
    wph
    @49
    @50
    @59
    simprd
    wph
    c1
    c1
    caddc
    co
    #
    cP
    clt
    wbr
    c1
    @1
    clt
    wbr
    wph
    @61
    c2
    cP
    clt
    df-2
    wph
    c2
    cP
    clt
    wbr
    cP
    c2
    wne
    #
    wph
    @17
    @62
    lgseisen.1
    cP
    cprime
    c2
    eldifsni
    syl
    wph
    c2
    cP
    @34
    wph
    2re
    a1i
    @60
    wph
    @31
    cP
    c2
    cuz
    cfv
    wcel
    c2
    cP
    cle
    wbr
    @32
    cP
    prmuz2
    c2
    cP
    eluzle
    3syl
    leltned
    mpbird
    syl5eqbrr
    wph
    c1
    c1
    cP
    @37
    @37
    @60
    ltaddsubd
    mpbid
    lelttrd
    wph
    @14
    c1
    cP
    @36
    @37
    @60
    ltaddsubd
    mpbird
    @20
    cP
    modid
    syl22anc
    eqtrd
    oveq1d
    wph
    @14
    cc
    wcel
    c1
    cc
    wcel
    @21
    @14
    wceq
    wph
    @14
    @36
    recnd
    ax-1cn
    @14
    c1
    pncan
    sylancl
    eqtrd
    eqtrd
end
