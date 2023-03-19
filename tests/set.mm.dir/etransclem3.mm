include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cfa.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cexp.mm"
include "cmul.mm"
include "cz.mm"
include "wa.mm"
include "0zd.mm"
include "wn.mm"
include "cfz.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "cle.mm"
include "nnzd.mm"
include "adantr.mm"
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
include "syl.mm"
include "nnred.mm"
include "subge02d.mm"
include "mpbid.mm"
include "jca32.mm"
include "elfz2.mm"
include "sylibr.mm"
include "permnn.mm"
include "cn0.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "zexpcl.mm"
include "syl2anc.mm"
include "zmulcld.mm"
include "ifclda.mm"

theorem etransclem3
  let wph: wff ph
  let cC: class C
  let cP: class P
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  assume etransclem3.n: |- ( ph -> P e. NN )
  assume etransclem3.c: |- ( ph -> C : ( 0 ... M ) --> ( 0 ... N ) )
  assume etransclem3.j: |- ( ph -> J e. ( 0 ... M ) )
  assume etransclem3.4: |- ( ph -> K e. ZZ )


  assert |- ( ph -> if ( P < ( C ` J ) , 0 , ( ( ( ! ` P ) / ( ! ` ( P - ( C ` J ) ) ) ) x. ( ( K - J ) ^ ( P - ( C ` J ) ) ) ) ) e. ZZ )

  proof
    wph
    cP
    cJ
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
    @0
    cmin
    co
    #
    cfa
    cfv
    cdiv
    co
    #
    cK
    cJ
    cmin
    co
    #
    @2
    cexp
    co
    #
    cmul
    co
    cz
    wph
    @1
    wa
    0zd
    wph
    @1
    wn
    #
    wa
    #
    @3
    @5
    @7
    @3
    @7
    @2
    cc0
    cP
    cfz
    co
    wcel
    #
    @3
    cn
    wcel
    @7
    cc0
    cz
    wcel
    #
    cP
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    w3a
    #
    cc0
    @2
    cle
    wbr
    #
    @2
    cP
    cle
    wbr
    #
    wa
    wa
    @8
    @7
    @12
    @13
    @14
    @7
    @9
    @10
    @11
    @7
    0zd
    wph
    @10
    @6
    wph
    cP
    etransclem3.n
    nnzd
    #
    adantr
    #
    wph
    @11
    @6
    wph
    cP
    @0
    @15
    wph
    @0
    cc0
    cN
    wph
    cc0
    cM
    cfz
    co
    cc0
    cN
    cfz
    co
    #
    cJ
    cC
    etransclem3.c
    etransclem3.j
    ffvelrnd
    #
    elfzelzd
    #
    zsubcld
    adantr
    #
    3jca
    @7
    @13
    @0
    cP
    cle
    wbr
    @7
    @0
    cP
    wph
    @0
    cr
    wcel
    @6
    wph
    @0
    @19
    zred
    #
    adantr
    #
    @7
    cP
    @16
    zred
    #
    wph
    @6
    simpr
    nltled
    @7
    cP
    @0
    @23
    @22
    subge0d
    mpbird
    #
    wph
    @14
    @6
    wph
    cc0
    @0
    cle
    wbr
    #
    @14
    wph
    @0
    @17
    wcel
    @25
    @18
    @0
    cc0
    cN
    elfzle1
    syl
    wph
    cP
    @0
    wph
    cP
    etransclem3.n
    nnred
    @21
    subge02d
    mpbid
    adantr
    jca32
    @2
    cc0
    cP
    elfz2
    sylibr
    @2
    cP
    permnn
    syl
    nnzd
    @7
    @4
    cz
    wcel
    #
    @2
    cn0
    wcel
    #
    @5
    cz
    wcel
    wph
    @26
    @6
    wph
    cK
    cJ
    etransclem3.4
    wph
    cJ
    cc0
    cM
    etransclem3.j
    elfzelzd
    zsubcld
    adantr
    @7
    @11
    @13
    @27
    @20
    @24
    @2
    elnn0z
    sylanbrc
    @4
    @2
    zexpcl
    syl2anc
    zmulcld
    ifclda
end
