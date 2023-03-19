include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cfa.mm"
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
include "cn0.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "nn0zd.mm"
include "cuz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "ffvelrnd.mm"
include "elfzelzd.mm"
include "zsubcld.mm"
include "3jca.mm"
include "adantr.mm"
include "cr.mm"
include "zred.mm"
include "nn0red.mm"
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
include "nnzd.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "zexpcl.mm"
include "syl2anc.mm"
include "zmulcld.mm"
include "ifclda.mm"

theorem etransclem10
  let wph: wff ph
  let cC: class C
  let cP: class P
  let cJ: class J
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  assume etransclem10.n: |- ( ph -> P e. NN )
  assume etransclem10.m: |- ( ph -> M e. NN0 )
  assume etransclem10.c: |- ( ph -> C : ( 0 ... M ) --> ( 0 ... N ) )
  assume etransclem10.j: |- ( ph -> J e. ZZ )


  assert |- ( ph -> if ( ( P - 1 ) < ( C ` 0 ) , 0 , ( ( ( ! ` ( P - 1 ) ) / ( ! ` ( ( P - 1 ) - ( C ` 0 ) ) ) ) x. ( J ^ ( ( P - 1 ) - ( C ` 0 ) ) ) ) ) e. ZZ )

  proof
    wph
    cP
    c1
    cmin
    co
    #
    cc0
    cC
    cfv
    #
    clt
    wbr
    #
    cc0
    @0
    cfa
    cfv
    @0
    @1
    cmin
    co
    #
    cfa
    cfv
    cdiv
    co
    #
    cJ
    @3
    cexp
    co
    #
    cmul
    co
    cz
    wph
    @2
    wa
    0zd
    wph
    @2
    wn
    #
    wa
    #
    @4
    @5
    @7
    @4
    @7
    @3
    cc0
    @0
    cfz
    co
    wcel
    #
    @4
    cn
    wcel
    @7
    cc0
    cz
    wcel
    #
    @0
    cz
    wcel
    #
    @3
    cz
    wcel
    #
    w3a
    #
    cc0
    @3
    cle
    wbr
    #
    @3
    @0
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
    wph
    @12
    @6
    wph
    @9
    @10
    @11
    wph
    0zd
    wph
    @0
    wph
    cP
    cn
    wcel
    @0
    cn0
    wcel
    etransclem10.n
    cP
    nnm1nn0
    syl
    #
    nn0zd
    #
    wph
    @0
    @1
    @16
    wph
    @1
    cc0
    cN
    wph
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
    cc0
    cC
    etransclem10.c
    wph
    cM
    cc0
    cuz
    cfv
    #
    wcel
    cc0
    @17
    wcel
    wph
    cM
    cn0
    @19
    etransclem10.m
    nn0uz
    syl6eleq
    cc0
    cM
    eluzfz1
    syl
    ffvelrnd
    #
    elfzelzd
    #
    zsubcld
    #
    3jca
    adantr
    @7
    @13
    @1
    @0
    cle
    wbr
    @7
    @1
    @0
    wph
    @1
    cr
    wcel
    @6
    wph
    @1
    @21
    zred
    adantr
    #
    wph
    @0
    cr
    wcel
    @6
    wph
    @0
    @15
    nn0red
    adantr
    #
    wph
    @6
    simpr
    nltled
    @7
    @0
    @1
    @24
    @23
    subge0d
    mpbird
    #
    @7
    cc0
    @1
    cle
    wbr
    #
    @14
    wph
    @26
    @6
    wph
    @1
    @18
    wcel
    @26
    @20
    @1
    cc0
    cN
    elfzle1
    syl
    adantr
    @7
    @0
    @1
    @24
    @23
    subge02d
    mpbid
    jca32
    @3
    cc0
    @0
    elfz2
    sylibr
    @3
    @0
    permnn
    syl
    nnzd
    @7
    cJ
    cz
    wcel
    #
    @3
    cn0
    wcel
    #
    @5
    cz
    wcel
    wph
    @27
    @6
    etransclem10.j
    adantr
    @7
    @11
    @13
    @28
    wph
    @11
    @6
    @22
    adantr
    @25
    @3
    elnn0z
    sylanbrc
    cJ
    @3
    zexpcl
    syl2anc
    zmulcld
    ifclda
end
