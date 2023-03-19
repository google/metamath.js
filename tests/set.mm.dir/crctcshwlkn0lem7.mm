include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cc0.mm"
include "cfzo.mm"
include "wral.mm"
include "cmin.mm"
include "cun.mm"
include "crctcshwlkn0lem4.mm"
include "eqidd.mm"
include "crctcshwlkn0lem6.mm"
include "mpdan.mm"
include "ovex.mm"
include "wkslem1.mm"
include "ralsn.mm"
include "sylibr.mm"
include "ralunb.mm"
include "sylanbrc.mm"
include "wcel.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "elfzo1.mm"
include "cuz.mm"
include "cn0.mm"
include "cz.mm"
include "cle.mm"
include "nnz.mm"
include "zsubcl.mm"
include "syl2anr.mm"
include "3adant3.mm"
include "cr.mm"
include "wi.mm"
include "nnre.mm"
include "wa.mm"
include "posdif.mm"
include "0re.mm"
include "resubcl.mm"
include "ancoms.mm"
include "ltle.mm"
include "sylancr.mm"
include "sylbid.mm"
include "syl2an.mm"
include "3impia.mm"
include "elnn0z.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "fzosplitsn.mm"
include "syl.mm"
include "sylbi.mm"
include "raleqdv.mm"
include "mpbird.mm"
include "crctcshwlkn0lem5.mm"
include "cfz.mm"
include "nnsub.mm"
include "biimp3a.mm"
include "nnnn0.mm"
include "peano2nn0.mm"
include "3syl.mm"
include "3ad2ant2.mm"
include "anim1i.mm"
include "crctcshwlkn0lem1.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "fzosplit.mm"

theorem crctcshwlkn0lem7
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cH: class H
  let cI: class I
  let cN: class N
  let cJ: class J
  assume crctcshwlkn0lem.s: |- ( ph -> S e. ( 1 ..^ N ) )
  assume crctcshwlkn0lem.q: |- Q = ( x e. ( 0 ... N ) |-> if ( x <_ ( N - S ) , ( P ` ( x + S ) ) , ( P ` ( ( x + S ) - N ) ) ) )
  assume crctcshwlkn0lem.h: |- H = ( F cyclShift S )
  assume crctcshwlkn0lem.n: |- N = ( # ` F )
  assume crctcshwlkn0lem.f: |- ( ph -> F e. Word A )
  assume crctcshwlkn0lem.p: |- ( ph -> A. i e. ( 0 ..^ N ) if- ( ( P ` i ) = ( P ` ( i + 1 ) ) , ( I ` ( F ` i ) ) = { ( P ` i ) } , { ( P ` i ) , ( P ` ( i + 1 ) ) } C_ ( I ` ( F ` i ) ) ) )
  assume crctcshwlkn0lem.e: |- ( ph -> ( P ` N ) = ( P ` 0 ) )

  disjoint N x
  disjoint P x
  disjoint S x
  disjoint ph x
  disjoint F i
  disjoint I i
  disjoint N i
  disjoint P i
  disjoint S i
  disjoint i ph
  disjoint j ph
  disjoint i j
  disjoint j x
  disjoint I j
  disjoint H j
  disjoint N j
  disjoint Q j
  disjoint S j
  disjoint J x
  assert |- ( ph -> A. j e. ( 0 ..^ N ) if- ( ( Q ` j ) = ( Q ` ( j + 1 ) ) , ( I ` ( H ` j ) ) = { ( Q ` j ) } , { ( Q ` j ) , ( Q ` ( j + 1 ) ) } C_ ( I ` ( H ` j ) ) ) )

  proof
    wph
    vj
    cv
    #
    cQ
    cfv
    #
    @0
    c1
    caddc
    co
    cQ
    cfv
    #
    wceq
    @0
    cH
    cfv
    cI
    cfv
    #
    @1
    csn
    wceq
    @1
    @2
    cpr
    @3
    wss
    wif
    #
    vj
    cc0
    cN
    cfzo
    co
    #
    wral
    @4
    vj
    cc0
    cN
    cS
    cmin
    co
    #
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @7
    cN
    cfzo
    co
    #
    cun
    #
    wral
    #
    wph
    @4
    vj
    @8
    wral
    #
    @4
    vj
    @9
    wral
    @11
    wph
    @12
    @4
    vj
    cc0
    @6
    cfzo
    co
    #
    @6
    csn
    #
    cun
    #
    wral
    #
    wph
    @4
    vj
    @13
    wral
    @4
    vj
    @14
    wral
    #
    @16
    wph
    vx
    cA
    cP
    cQ
    cS
    vi
    vj
    cF
    cH
    cI
    cN
    crctcshwlkn0lem.s
    crctcshwlkn0lem.q
    crctcshwlkn0lem.h
    crctcshwlkn0lem.n
    crctcshwlkn0lem.f
    crctcshwlkn0lem.p
    crctcshwlkn0lem4
    wph
    @6
    cQ
    cfv
    #
    @7
    cQ
    cfv
    #
    wceq
    @6
    cH
    cfv
    cI
    cfv
    #
    @18
    csn
    wceq
    @18
    @19
    cpr
    @20
    wss
    wif
    #
    @17
    wph
    @6
    @6
    wceq
    @21
    wph
    @6
    eqidd
    wph
    vx
    cA
    cP
    cQ
    cS
    vi
    cF
    cH
    cI
    @6
    cN
    crctcshwlkn0lem.s
    crctcshwlkn0lem.q
    crctcshwlkn0lem.h
    crctcshwlkn0lem.n
    crctcshwlkn0lem.f
    crctcshwlkn0lem.p
    crctcshwlkn0lem.e
    crctcshwlkn0lem6
    mpdan
    @4
    @21
    vj
    @6
    cN
    cS
    cmin
    ovex
    @0
    @6
    cQ
    cH
    cI
    wkslem1
    ralsn
    sylibr
    @4
    vj
    @13
    @14
    ralunb
    sylanbrc
    wph
    @4
    vj
    @8
    @15
    wph
    cS
    c1
    cN
    cfzo
    co
    wcel
    #
    @8
    @15
    wceq
    #
    crctcshwlkn0lem.s
    @22
    cS
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    cS
    cN
    clt
    wbr
    #
    w3a
    #
    @23
    cN
    cS
    elfzo1
    #
    @27
    @6
    cc0
    cuz
    cfv
    wcel
    #
    @23
    @27
    @6
    cn0
    wcel
    #
    @29
    @27
    @6
    cz
    wcel
    #
    cc0
    @6
    cle
    wbr
    #
    @30
    @24
    @25
    @31
    @26
    @25
    cN
    cz
    wcel
    cS
    cz
    wcel
    @31
    @24
    cN
    nnz
    cS
    nnz
    cN
    cS
    zsubcl
    syl2anr
    3adant3
    @24
    @25
    @26
    @32
    @24
    cS
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @26
    @32
    wi
    @25
    cS
    nnre
    cN
    nnre
    #
    @33
    @34
    wa
    #
    @26
    cc0
    @6
    clt
    wbr
    #
    @32
    cS
    cN
    posdif
    @36
    cc0
    cr
    wcel
    @6
    cr
    wcel
    #
    @37
    @32
    wi
    0re
    @34
    @33
    @38
    cN
    cS
    resubcl
    ancoms
    cc0
    @6
    ltle
    sylancr
    sylbid
    syl2an
    3impia
    @6
    elnn0z
    sylanbrc
    @6
    elnn0uz
    sylib
    cc0
    @6
    fzosplitsn
    syl
    sylbi
    syl
    raleqdv
    mpbird
    wph
    vx
    cA
    cP
    cQ
    cS
    vi
    vj
    cF
    cH
    cI
    cN
    crctcshwlkn0lem.s
    crctcshwlkn0lem.q
    crctcshwlkn0lem.h
    crctcshwlkn0lem.n
    crctcshwlkn0lem.f
    crctcshwlkn0lem.p
    crctcshwlkn0lem5
    @4
    vj
    @8
    @9
    ralunb
    sylanbrc
    wph
    @4
    vj
    @5
    @10
    wph
    @22
    @7
    cc0
    cN
    cfz
    co
    wcel
    #
    @5
    @10
    wceq
    crctcshwlkn0lem.s
    @22
    @27
    @39
    @28
    @27
    @7
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    @7
    cN
    cle
    wbr
    #
    @39
    @27
    @6
    cn
    wcel
    #
    @30
    @40
    @24
    @25
    @26
    @43
    cS
    cN
    nnsub
    biimp3a
    @6
    nnnn0
    @6
    peano2nn0
    3syl
    @25
    @24
    @41
    @26
    cN
    nnnn0
    3ad2ant2
    @24
    @25
    @42
    @26
    @24
    @25
    wa
    @34
    @24
    wa
    #
    @42
    @25
    @24
    @44
    @25
    @34
    @24
    @35
    anim1i
    ancoms
    cN
    cS
    crctcshwlkn0lem1
    syl
    3adant3
    @7
    cN
    elfz2nn0
    syl3anbrc
    sylbi
    cc0
    cN
    @7
    fzosplit
    3syl
    raleqdv
    mpbird
end
