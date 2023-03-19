include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cfa.mm"
include "cmin.mm"
include "cdiv.mm"
include "cexp.mm"
include "cmul.mm"
include "cif.mm"
include "fzfid.mm"
include "wcel.mm"
include "wa.mm"
include "cz.mm"
include "0zd.mm"
include "wn.mm"
include "cn.mm"
include "w3a.mm"
include "cle.mm"
include "nnzd.mm"
include "ad2antrr.mm"
include "adantr.mm"
include "wf.mm"
include "caddc.mm"
include "wss.mm"
include "fzp1ss.mm"
include "syl.mm"
include "id.mm"
include "1e0p1.mm"
include "oveq1i.mm"
include "syl6eleq.mm"
include "sseldd.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "elfzelzd.mm"
include "zsubcld.mm"
include "3jca.mm"
include "cr.mm"
include "zred.mm"
include "simpr.mm"
include "nltled.mm"
include "subge0d.mm"
include "mpbird.mm"
include "elfzle1.mm"
include "subge02d.mm"
include "mpbid.mm"
include "jca32.mm"
include "elfz2.mm"
include "sylibr.mm"
include "permnn.mm"
include "cn0.mm"
include "elfzelz.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "zexpcl.mm"
include "syl2anc.mm"
include "zmulcld.mm"
include "ifclda.mm"
include "fprodzcl.mm"

theorem etransclem7
  let wph: wff ph
  let cC: class C
  let cP: class P
  let vj: setvar j
  let cJ: class J
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  assume etransclem7.n: |- ( ph -> P e. NN )
  assume etransclem7.c: |- ( ph -> C : ( 0 ... M ) --> ( 0 ... N ) )
  assume etransclem7.j: |- ( ph -> J e. ( 0 ... M ) )

  disjoint M j
  disjoint j ph
  disjoint k x
  assert |- ( ph -> prod_ j e. ( 1 ... M ) if ( P < ( C ` j ) , 0 , ( ( ( ! ` P ) / ( ! ` ( P - ( C ` j ) ) ) ) x. ( ( J - j ) ^ ( P - ( C ` j ) ) ) ) ) e. ZZ )

  proof
    wph
    c1
    cM
    cfz
    co
    #
    cP
    vj
    cv
    #
    cC
    cfv
    #
    clt
    wbr
    #
    cc0
    cP
    cfa
    cfv
    cP
    @2
    cmin
    co
    #
    cfa
    cfv
    cdiv
    co
    #
    cJ
    @1
    cmin
    co
    #
    @4
    cexp
    co
    #
    cmul
    co
    #
    cif
    vj
    wph
    c1
    cM
    fzfid
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @3
    cc0
    @8
    cz
    @10
    @3
    wa
    0zd
    @10
    @3
    wn
    #
    wa
    #
    @5
    @7
    @12
    @5
    @12
    @4
    cc0
    cP
    cfz
    co
    wcel
    #
    @5
    cn
    wcel
    @12
    cc0
    cz
    wcel
    #
    cP
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    w3a
    #
    cc0
    @4
    cle
    wbr
    #
    @4
    cP
    cle
    wbr
    #
    wa
    wa
    @13
    @12
    @17
    @18
    @19
    @12
    @14
    @15
    @16
    @12
    0zd
    wph
    @15
    @9
    @11
    wph
    cP
    etransclem7.n
    nnzd
    #
    ad2antrr
    #
    @10
    @16
    @11
    @10
    cP
    @2
    wph
    @15
    @9
    @20
    adantr
    @10
    @2
    cc0
    cN
    @10
    cc0
    cM
    cfz
    co
    #
    cc0
    cN
    cfz
    co
    #
    @1
    cC
    wph
    @22
    @23
    cC
    wf
    @9
    etransclem7.c
    adantr
    @9
    @1
    @22
    wcel
    wph
    @9
    cc0
    c1
    caddc
    co
    #
    cM
    cfz
    co
    #
    @22
    @1
    @9
    @14
    @25
    @22
    wss
    @9
    0zd
    cc0
    cM
    fzp1ss
    syl
    @9
    @1
    @0
    @25
    @9
    id
    c1
    @24
    cM
    cfz
    1e0p1
    oveq1i
    syl6eleq
    sseldd
    adantl
    ffvelrnd
    #
    elfzelzd
    #
    zsubcld
    adantr
    #
    3jca
    @12
    @18
    @2
    cP
    cle
    wbr
    @12
    @2
    cP
    @10
    @2
    cr
    wcel
    @11
    @10
    @2
    @27
    zred
    adantr
    #
    @12
    cP
    @21
    zred
    #
    @10
    @11
    simpr
    nltled
    @12
    cP
    @2
    @30
    @29
    subge0d
    mpbird
    #
    @12
    cc0
    @2
    cle
    wbr
    #
    @19
    @10
    @32
    @11
    @10
    @2
    @23
    wcel
    @32
    @26
    @2
    cc0
    cN
    elfzle1
    syl
    adantr
    @12
    cP
    @2
    @30
    @29
    subge02d
    mpbid
    jca32
    @4
    cc0
    cP
    elfz2
    sylibr
    @4
    cP
    permnn
    syl
    nnzd
    @12
    @6
    cz
    wcel
    #
    @4
    cn0
    wcel
    #
    @7
    cz
    wcel
    @10
    @33
    @11
    @10
    cJ
    @1
    wph
    cJ
    cz
    wcel
    @9
    wph
    cJ
    cc0
    cM
    etransclem7.j
    elfzelzd
    adantr
    @9
    @1
    cz
    wcel
    wph
    @1
    c1
    cM
    elfzelz
    adantl
    zsubcld
    adantr
    @12
    @16
    @18
    @34
    @28
    @31
    @4
    elnn0z
    sylanbrc
    @6
    @4
    zexpcl
    syl2anc
    zmulcld
    ifclda
    fprodzcl
end
