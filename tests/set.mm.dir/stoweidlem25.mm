include "cv.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "cexp.mm"
include "cdiv.mm"
include "cr.mm"
include "eldifi.mm"
include "cmin.mm"
include "nnnn0d.mm"
include "stoweidlem12.mm"
include "1red.mm"
include "ffvelrnda.mm"
include "cn0.mm"
include "adantr.mm"
include "reexpcld.mm"
include "resubcld.mm"
include "nnexpcld.mm"
include "eqeltrd.mm"
include "sylan2.mm"
include "nnred.mm"
include "rpred.mm"
include "remulcld.mm"
include "cc0.mm"
include "wne.mm"
include "cc.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "rpcnne0d.mm"
include "mulne0.mm"
include "syl21anc.mm"
include "cn.mm"
include "wb.mm"
include "rpcnd.mm"
include "mulcld.mm"
include "expne0.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "rereccld.mm"
include "cle.mm"
include "wceq.mm"
include "crp.mm"
include "wf.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "0red.mm"
include "clt.mm"
include "wbr.mm"
include "rpgt0d.mm"
include "r19.21bi.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "wral.mm"
include "rsp.mm"
include "sylc.mm"
include "simpld.mm"
include "simprd.mm"
include "stoweidlem1.mm"
include "eqbrtrd.mm"
include "lelttrd.mm"

theorem stoweidlem25
  let wph: wff ph
  let vt: setvar t
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cU: class U
  let cE: class E
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  assume stoweidlem25.1: |- Q = ( t e. T |-> ( ( 1 - ( ( P ` t ) ^ N ) ) ^ ( K ^ N ) ) )
  assume stoweidlem25.2: |- ( ph -> N e. NN )
  assume stoweidlem25.3: |- ( ph -> K e. NN )
  assume stoweidlem25.4: |- ( ph -> D e. RR+ )
  assume stoweidlem25.6: |- ( ph -> P : T --> RR )
  assume stoweidlem25.7: |- ( ph -> A. t e. T ( 0 <_ ( P ` t ) /\ ( P ` t ) <_ 1 ) )
  assume stoweidlem25.8: |- ( ph -> A. t e. ( T \ U ) D <_ ( P ` t ) )
  assume stoweidlem25.9: |- ( ph -> E e. RR+ )
  assume stoweidlem25.11: |- ( ph -> ( 1 / ( ( K x. D ) ^ N ) ) < E )

  disjoint T t
  disjoint k x
  assert |- ( ( ph /\ t e. ( T \ U ) ) -> ( Q ` t ) < E )

  proof
    wph
    vt
    cv
    #
    cT
    cU
    cdif
    #
    wcel
    #
    wa
    #
    @0
    cQ
    cfv
    #
    c1
    cK
    cD
    cmul
    co
    #
    cN
    cexp
    co
    #
    cdiv
    co
    #
    cE
    @2
    wph
    @0
    cT
    wcel
    #
    @4
    cr
    wcel
    @0
    cT
    cU
    eldifi
    #
    wph
    @8
    wa
    #
    @4
    c1
    @0
    cP
    cfv
    #
    cN
    cexp
    co
    #
    cmin
    co
    #
    cK
    cN
    cexp
    co
    #
    cexp
    co
    #
    cr
    wph
    vt
    cP
    cQ
    cT
    cK
    cN
    stoweidlem25.1
    stoweidlem25.6
    wph
    cN
    stoweidlem25.2
    nnnn0d
    #
    wph
    cK
    stoweidlem25.3
    nnnn0d
    stoweidlem12
    #
    @10
    @13
    @14
    @10
    c1
    @12
    @10
    1red
    @10
    @11
    cN
    wph
    cT
    cr
    @0
    cP
    stoweidlem25.6
    ffvelrnda
    wph
    cN
    cn0
    wcel
    @8
    @16
    adantr
    reexpcld
    resubcld
    wph
    @14
    cn0
    wcel
    @8
    wph
    @14
    wph
    cK
    cN
    stoweidlem25.3
    @16
    nnexpcld
    nnnn0d
    adantr
    reexpcld
    eqeltrd
    sylan2
    wph
    @7
    cr
    wcel
    @2
    wph
    @6
    wph
    @5
    cN
    wph
    cK
    cD
    wph
    cK
    stoweidlem25.3
    nnred
    wph
    cD
    stoweidlem25.4
    rpred
    #
    remulcld
    @16
    reexpcld
    wph
    @6
    cc0
    wne
    #
    @5
    cc0
    wne
    #
    wph
    cK
    cc
    wcel
    cK
    cc0
    wne
    cD
    cc
    wcel
    cD
    cc0
    wne
    wa
    @20
    wph
    cK
    stoweidlem25.3
    nncnd
    #
    wph
    cK
    stoweidlem25.3
    nnne0d
    wph
    cD
    stoweidlem25.4
    rpcnne0d
    cK
    cD
    mulne0
    syl21anc
    wph
    @5
    cc
    wcel
    cN
    cn
    wcel
    #
    @19
    @20
    wb
    wph
    cK
    cD
    @21
    wph
    cD
    stoweidlem25.4
    rpcnd
    mulcld
    stoweidlem25.2
    @5
    cN
    expne0
    syl2anc
    mpbird
    rereccld
    adantr
    wph
    cE
    cr
    wcel
    @2
    wph
    cE
    stoweidlem25.9
    rpred
    adantr
    @3
    @4
    @15
    @7
    cle
    @2
    wph
    @8
    @4
    @15
    wceq
    @9
    @17
    sylan2
    @3
    @11
    cD
    cK
    cN
    wph
    @22
    @2
    stoweidlem25.2
    adantr
    wph
    cK
    cn
    wcel
    @2
    stoweidlem25.3
    adantr
    wph
    cD
    crp
    wcel
    @2
    stoweidlem25.4
    adantr
    @3
    @11
    @3
    cT
    cr
    @0
    cP
    wph
    cT
    cr
    cP
    wf
    @2
    stoweidlem25.6
    adantr
    @2
    @8
    wph
    @9
    adantl
    #
    ffvelrnd
    #
    @3
    cc0
    cD
    @11
    @3
    0red
    wph
    cD
    cr
    wcel
    @2
    @18
    adantr
    @24
    wph
    cc0
    cD
    clt
    wbr
    @2
    wph
    cD
    stoweidlem25.4
    rpgt0d
    adantr
    wph
    cD
    @11
    cle
    wbr
    vt
    @1
    stoweidlem25.8
    r19.21bi
    #
    ltletrd
    elrpd
    @3
    cc0
    @11
    cle
    wbr
    #
    @11
    c1
    cle
    wbr
    #
    @3
    @26
    @27
    wa
    #
    vt
    cT
    wral
    #
    @8
    @28
    wph
    @29
    @2
    stoweidlem25.7
    adantr
    @23
    @28
    vt
    cT
    rsp
    sylc
    #
    simpld
    @3
    @26
    @27
    @30
    simprd
    @25
    stoweidlem1
    eqbrtrd
    wph
    @7
    cE
    clt
    wbr
    @2
    stoweidlem25.11
    adantr
    lelttrd
end
