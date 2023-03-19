include "ce.mm"
include "caddc.mm"
include "c1.mm"
include "cseq.mm"
include "ccom.mm"
include "clgam.mm"
include "cfv.mm"
include "clog.mm"
include "co.mm"
include "cgam.mm"
include "cmul.mm"
include "cli.mm"
include "cc.mm"
include "cn.mm"
include "nnuz.mm"
include "1zzd.mm"
include "ccncf.mm"
include "wcel.mm"
include "efcn.mm"
include "a1i.mm"
include "cv.mm"
include "cdiv.mm"
include "cmin.mm"
include "wa.mm"
include "cz.mm"
include "cdif.mm"
include "eldifad.mm"
include "adantr.mm"
include "simpr.mm"
include "peano2nnd.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "relogcld.mm"
include "recnd.mm"
include "mulcld.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcld.mm"
include "1cnd.mm"
include "addcld.mm"
include "dmgmdivn0.mm"
include "logcld.mm"
include "subcld.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "serf.mm"
include "lgamcvg.mm"
include "lgamcl.mm"
include "syl.mm"
include "dmgmn0.mm"
include "climcncf.mm"
include "wceq.mm"
include "efadd.mm"
include "syl2anc.mm"
include "eflgam.mm"
include "cc0.mm"
include "wne.mm"
include "eflog.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "breqtrd.mm"

theorem gamcvg
  let wph: wff ph
  let cA: class A
  let vm: setvar m
  let cG: class G
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume lgamcvg.g: |- G = ( m e. NN |-> ( ( A x. ( log ` ( ( m + 1 ) / m ) ) ) - ( log ` ( ( A / m ) + 1 ) ) ) )
  assume lgamcvg.a: |- ( ph -> A e. ( CC \ ( ZZ \ NN ) ) )

  disjoint A m
  disjoint m ph
  disjoint k m
  disjoint k n
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint G k
  disjoint G n
  disjoint G y
  disjoint k ph
  disjoint n ph
  disjoint ph r
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( exp o. seq 1 ( + , G ) ) ~~> ( ( _G ` A ) x. A ) )

  proof
    wph
    ce
    caddc
    cG
    c1
    cseq
    #
    ccom
    cA
    clgam
    cfv
    #
    cA
    clog
    cfv
    #
    caddc
    co
    #
    ce
    cfv
    #
    cA
    cgam
    cfv
    #
    cA
    cmul
    co
    #
    cli
    wph
    cc
    cc
    @3
    ce
    @0
    c1
    cn
    nnuz
    wph
    1zzd
    #
    ce
    cc
    cc
    ccncf
    co
    wcel
    wph
    efcn
    a1i
    wph
    vn
    cG
    c1
    cn
    nnuz
    @7
    wph
    cn
    cc
    vn
    cv
    cG
    wph
    vm
    cn
    cA
    vm
    cv
    #
    c1
    caddc
    co
    #
    @8
    cdiv
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    cA
    @8
    cdiv
    co
    #
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    cc
    cG
    wph
    @8
    cn
    wcel
    #
    wa
    #
    @12
    @15
    @17
    cA
    @11
    wph
    cA
    cc
    wcel
    #
    @16
    wph
    cA
    cc
    cz
    cn
    cdif
    #
    lgamcvg.a
    eldifad
    #
    adantr
    #
    @17
    @11
    @17
    @10
    @17
    @9
    @8
    @17
    @9
    @17
    @8
    wph
    @16
    simpr
    #
    peano2nnd
    nnrpd
    @17
    @8
    @22
    nnrpd
    rpdivcld
    relogcld
    recnd
    mulcld
    @17
    @14
    @17
    @13
    c1
    @17
    cA
    @8
    @21
    @17
    @8
    @22
    nncnd
    @17
    @8
    @22
    nnne0d
    divcld
    @17
    1cnd
    addcld
    @17
    cA
    @8
    wph
    cA
    cc
    @19
    cdif
    wcel
    #
    @16
    lgamcvg.a
    adantr
    @22
    dmgmdivn0
    logcld
    subcld
    lgamcvg.g
    fmptd
    ffvelrnda
    serf
    wph
    cA
    vm
    cG
    lgamcvg.g
    lgamcvg.a
    lgamcvg
    wph
    @1
    @2
    wph
    @23
    @1
    cc
    wcel
    #
    lgamcvg.a
    cA
    lgamcl
    syl
    #
    wph
    cA
    @20
    wph
    cA
    lgamcvg.a
    dmgmn0
    #
    logcld
    #
    addcld
    climcncf
    wph
    @4
    @1
    ce
    cfv
    #
    @2
    ce
    cfv
    #
    cmul
    co
    #
    @6
    wph
    @24
    @2
    cc
    wcel
    @4
    @30
    wceq
    @25
    @27
    @1
    @2
    efadd
    syl2anc
    wph
    @28
    @5
    @29
    cA
    cmul
    wph
    @23
    @28
    @5
    wceq
    lgamcvg.a
    cA
    eflgam
    syl
    wph
    @18
    cA
    cc0
    wne
    @29
    cA
    wceq
    @20
    @26
    cA
    eflog
    syl2anc
    oveq12d
    eqtrd
    breqtrd
end
