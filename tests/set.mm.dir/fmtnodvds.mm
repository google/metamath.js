include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cfmtno.mm"
include "cfv.mm"
include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cv.mm"
include "cprod.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "cle.mm"
include "simpl.mm"
include "nn0nnaddcl.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "1red.mm"
include "cr.mm"
include "nnre.mm"
include "adantl.mm"
include "nn0re.mm"
include "adantr.mm"
include "nnge1.mm"
include "leadd2dd.mm"
include "wb.mm"
include "readdcl.mm"
include "syl2an.mm"
include "leaddsub.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "fzfid.mm"
include "wss.mm"
include "fz0ssnn0.mm"
include "a1i.mm"
include "cexp.mm"
include "cz.mm"
include "2nn0.mm"
include "id.mm"
include "nn0expcld.mm"
include "nn0zd.mm"
include "peano2zd.mm"
include "df-fmtno.mm"
include "fmptd.mm"
include "fprodfvdvdsd.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "elfznn0.mm"
include "fmtnonn.mm"
include "nncnd.mm"
include "fprodcl.mm"
include "2cnd.mm"
include "cc.mm"
include "nn0cn.mm"
include "nncn.mm"
include "addcl.mm"
include "npcan1.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "fmtnorec2.mm"
include "eqtrd.mm"
include "mvrraddd.mm"
include "breqtrrd.mm"

theorem fmtnodvds
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x


  assert |- ( ( N e. NN0 /\ M e. NN ) -> ( FermatNo ` N ) || ( ( FermatNo ` ( N + M ) ) - 2 ) )

  proof
    cN
    cn0
    wcel
    #
    cM
    cn
    wcel
    #
    wa
    #
    cN
    cfmtno
    cfv
    #
    cc0
    cN
    cM
    caddc
    co
    #
    c1
    cmin
    co
    #
    cfz
    co
    #
    vk
    cv
    #
    cfmtno
    cfv
    #
    vk
    cprod
    #
    @4
    cfmtno
    cfv
    #
    c2
    cmin
    co
    cdvds
    @2
    cN
    @6
    wcel
    #
    vn
    cv
    #
    cfmtno
    cfv
    #
    @9
    cdvds
    wbr
    #
    vn
    @6
    wral
    @3
    @9
    cdvds
    wbr
    #
    @2
    @0
    @5
    cn0
    wcel
    #
    cN
    @5
    cle
    wbr
    #
    @11
    @0
    @1
    simpl
    @2
    @4
    cn
    wcel
    @16
    cN
    cM
    nn0nnaddcl
    @4
    nnm1nn0
    syl
    #
    @2
    cN
    c1
    caddc
    co
    @4
    cle
    wbr
    #
    @17
    @2
    c1
    cM
    cN
    @2
    1red
    #
    @1
    cM
    cr
    wcel
    #
    @0
    cM
    nnre
    #
    adantl
    @0
    cN
    cr
    wcel
    #
    @1
    cN
    nn0re
    #
    adantr
    #
    @1
    c1
    cM
    cle
    wbr
    @0
    cM
    nnge1
    adantl
    leadd2dd
    @2
    @23
    c1
    cr
    wcel
    @4
    cr
    wcel
    #
    @19
    @17
    wb
    @25
    @20
    @0
    @23
    @21
    @26
    @1
    @24
    @22
    cN
    cM
    readdcl
    syl2an
    cN
    c1
    @4
    leaddsub
    syl3anc
    mpbid
    cN
    @5
    elfz2nn0
    syl3anbrc
    @2
    vn
    @6
    cn0
    vk
    cfmtno
    @2
    cc0
    @5
    fzfid
    #
    @6
    cn0
    wss
    @2
    @5
    fz0ssnn0
    a1i
    @2
    vn
    cn0
    c2
    c2
    @12
    cexp
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    #
    cz
    cfmtno
    @12
    cn0
    wcel
    #
    @30
    cz
    wcel
    @2
    @31
    @29
    @31
    @29
    @31
    c2
    @28
    c2
    cn0
    wcel
    @31
    2nn0
    a1i
    #
    @31
    c2
    @12
    @32
    @31
    id
    nn0expcld
    nn0expcld
    nn0zd
    peano2zd
    adantl
    vn
    df-fmtno
    fmptd
    fprodfvdvdsd
    @14
    @15
    vn
    cN
    @6
    @12
    cN
    wceq
    @13
    @3
    @9
    cdvds
    @12
    cN
    cfmtno
    fveq2
    breq1d
    rspcv
    sylc
    @2
    @10
    @9
    c2
    @2
    @6
    @8
    vk
    @27
    @2
    @7
    @6
    wcel
    #
    wa
    #
    @8
    @34
    @7
    cn0
    wcel
    #
    @8
    cn
    wcel
    @33
    @35
    @2
    @7
    @5
    elfznn0
    adantl
    @7
    fmtnonn
    syl
    nncnd
    fprodcl
    @2
    2cnd
    @2
    @10
    @5
    c1
    caddc
    co
    #
    cfmtno
    cfv
    #
    @9
    c2
    caddc
    co
    #
    @2
    @4
    @36
    cfmtno
    @2
    @36
    @4
    @2
    @4
    cc
    wcel
    #
    @36
    @4
    wceq
    @0
    cN
    cc
    wcel
    cM
    cc
    wcel
    @39
    @1
    cN
    nn0cn
    cM
    nncn
    cN
    cM
    addcl
    syl2an
    @4
    npcan1
    syl
    eqcomd
    fveq2d
    @2
    @16
    @37
    @38
    wceq
    @18
    vk
    @5
    fmtnorec2
    syl
    eqtrd
    mvrraddd
    breqtrrd
end
