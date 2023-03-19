include "cv.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "ccsh.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cmin.mm"
include "wi.mm"
include "fznn0sub2.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "syl5ibr.mm"
include "syl11.mm"
include "adantr.mm"
include "impcom.mm"
include "caddc.mm"
include "cword.mm"
include "cz.mm"
include "w3a.mm"
include "simpl.mm"
include "elfzelz.mm"
include "adantl.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "elfz2nn0.mm"
include "nn0z.mm"
include "zsubcl.mm"
include "syl2anr.mm"
include "3adant3.mm"
include "sylbi.mm"
include "3jca.mm"
include "sylan.mm"
include "2cshw.mm"
include "syl.mm"
include "cc.mm"
include "nn0cn.mm"
include "anim12i.mm"
include "pncan3.mm"
include "oveq2d.mm"
include "cshwn.mm"
include "3eqtrrd.mm"
include "adantrr.mm"
include "wb.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "mpbird.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"

theorem cshwcshid
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let vn: setvar n
  let cV: class V
  assume cshwcshid.1: |- ( ph -> y e. Word V )
  assume cshwcshid.2: |- ( ph -> ( # ` x ) = ( # ` y ) )

  disjoint m n
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint x y
  assert |- ( ph -> ( ( m e. ( 0 ... ( # ` y ) ) /\ x = ( y cyclShift m ) ) -> E. n e. ( 0 ... ( # ` x ) ) y = ( x cyclShift n ) ) )

  proof
    wph
    vm
    cv
    #
    cc0
    vy
    cv
    #
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    vx
    cv
    #
    @1
    @0
    ccsh
    co
    #
    wceq
    #
    wa
    #
    @1
    @5
    vn
    cv
    #
    ccsh
    co
    #
    wceq
    #
    vn
    cc0
    @5
    chash
    cfv
    #
    cfz
    co
    #
    wrex
    #
    wph
    @8
    wa
    #
    @2
    @0
    cmin
    co
    #
    @13
    wcel
    #
    @1
    @5
    @16
    ccsh
    co
    #
    wceq
    #
    @14
    @8
    wph
    @17
    @4
    wph
    @17
    wi
    @7
    @12
    @2
    wceq
    #
    @4
    @17
    wph
    @4
    @17
    @20
    @16
    @3
    wcel
    @0
    @2
    fznn0sub2
    @20
    @13
    @3
    @16
    @12
    @2
    cc0
    cfz
    oveq2
    eleq2d
    syl5ibr
    cshwcshid.2
    syl11
    adantr
    impcom
    @15
    @19
    @1
    @6
    @16
    ccsh
    co
    #
    wceq
    #
    wph
    @4
    @22
    @7
    wph
    @4
    wa
    #
    @21
    @1
    @0
    @16
    caddc
    co
    #
    ccsh
    co
    #
    @1
    @2
    ccsh
    co
    #
    @1
    @23
    @1
    cV
    cword
    wcel
    #
    @0
    cz
    wcel
    #
    @16
    cz
    wcel
    #
    w3a
    #
    @21
    @25
    wceq
    wph
    @27
    @4
    @30
    cshwcshid.1
    @27
    @4
    wa
    @27
    @28
    @29
    @27
    @4
    simpl
    @4
    @28
    @27
    @0
    cc0
    @2
    elfzelz
    adantl
    @4
    @29
    @27
    @4
    @0
    cn0
    wcel
    #
    @2
    cn0
    wcel
    #
    @0
    @2
    cle
    wbr
    #
    w3a
    #
    @29
    @0
    @2
    elfz2nn0
    #
    @31
    @32
    @29
    @33
    @32
    @2
    cz
    wcel
    @28
    @29
    @31
    @2
    nn0z
    @0
    nn0z
    @2
    @0
    zsubcl
    syl2anr
    3adant3
    sylbi
    adantl
    3jca
    sylan
    @0
    @16
    cV
    @1
    2cshw
    syl
    @23
    @24
    @2
    @1
    ccsh
    @4
    @24
    @2
    wceq
    #
    wph
    @4
    @0
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    wa
    #
    @36
    @4
    @34
    @39
    @35
    @31
    @32
    @39
    @33
    @31
    @37
    @32
    @38
    @0
    nn0cn
    @2
    nn0cn
    anim12i
    3adant3
    sylbi
    @0
    @2
    pncan3
    syl
    adantl
    oveq2d
    wph
    @26
    @1
    wceq
    #
    @4
    wph
    @27
    @40
    cshwcshid.1
    cV
    @1
    cshwn
    syl
    adantr
    3eqtrrd
    adantrr
    @8
    @19
    @22
    wb
    #
    wph
    @7
    @41
    @4
    @7
    @18
    @21
    @1
    @5
    @6
    @16
    ccsh
    oveq1
    eqeq2d
    adantl
    adantl
    mpbird
    @11
    @19
    vn
    @16
    @13
    @9
    @16
    wceq
    @10
    @18
    @1
    @9
    @16
    @5
    ccsh
    oveq2
    eqeq2d
    rspcev
    syl2anc
    ex
end
