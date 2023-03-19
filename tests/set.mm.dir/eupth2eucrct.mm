include "ceupth.mm"
include "cfv.mm"
include "wbr.mm"
include "ccrcts.mm"
include "wa.mm"
include "eupthp1.mm"
include "simpr.mm"
include "ctrls.mm"
include "cc0.mm"
include "chash.mm"
include "wceq.mm"
include "eupthistrl.mm"
include "adantl.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "cwlks.mm"
include "eupthiswlk.mm"
include "syl.mm"
include "ciedg.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "a1i.mm"
include "cvtx.mm"
include "wlkp1lem5.mm"
include "cdm.mm"
include "cword.mm"
include "wcel.mm"
include "wlkf.mm"
include "cn0.mm"
include "lencl.mm"
include "eleq1i.mm"
include "0elfz.mm"
include "sylbir.mm"
include "3syl.mm"
include "rspcdva.mm"
include "adantr.mm"
include "eqcomd.mm"
include "c1.mm"
include "caddc.mm"
include "fveq2i.mm"
include "cfn.mm"
include "cin.mm"
include "c0.mm"
include "wrdfin.mm"
include "snfi.mm"
include "wn.mm"
include "cfzo.mm"
include "wrddm.mm"
include "fzonel.mm"
include "sylnibr.mm"
include "eleq2.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "opeldmd.mm"
include "nsyld.mm"
include "mpd.mm"
include "disjsn.mm"
include "sylibr.mm"
include "hashun.mm"
include "syl3anc.mm"
include "eqcomi.mm"
include "opex.mm"
include "hashsng.mm"
include "ax-mp.mm"
include "oveq12i.mm"
include "3eqtrd.mm"
include "fveq12d.mm"
include "w3a.mm"
include "ovexd.mm"
include "wlkp1lem1.mm"
include "3jca.mm"
include "fsnunfv.mm"
include "eqtr2d.mm"
include "iscrct.mm"
include "sylanbrc.mm"
include "jca.mm"
include "mpdan.mm"

theorem eupth2eucrct
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  let vk: setvar k
  assume eupthp1.v: |- V = ( Vtx ` G )
  assume eupthp1.i: |- I = ( iEdg ` G )
  assume eupthp1.f: |- ( ph -> Fun I )
  assume eupthp1.a: |- ( ph -> I e. Fin )
  assume eupthp1.b: |- ( ph -> B e. _V )
  assume eupthp1.c: |- ( ph -> C e. V )
  assume eupthp1.d: |- ( ph -> -. B e. dom I )
  assume eupthp1.p: |- ( ph -> F ( EulerPaths ` G ) P )
  assume eupthp1.n: |- N = ( # ` F )
  assume eupthp1.e: |- ( ph -> E e. ( Edg ` G ) )
  assume eupthp1.x: |- ( ph -> { ( P ` N ) , C } C_ E )
  assume eupthp1.u: |- ( iEdg ` S ) = ( I u. { <. B , E >. } )
  assume eupthp1.h: |- H = ( F u. { <. N , B >. } )
  assume eupthp1.q: |- Q = ( P u. { <. ( N + 1 ) , C >. } )
  assume eupthp1.s: |- ( Vtx ` S ) = V
  assume eupthp1.l: |- ( ( ph /\ C = ( P ` N ) ) -> E = { C } )
  assume eupth2eucrct.c: |- ( ph -> C = ( P ` 0 ) )


  assert |- ( ph -> ( H ( EulerPaths ` S ) Q /\ H ( Circuits ` S ) Q ) )

  proof
    wph
    cH
    cQ
    cS
    ceupth
    cfv
    wbr
    #
    @0
    cH
    cQ
    cS
    ccrcts
    cfv
    wbr
    #
    wa
    wph
    cB
    cC
    cP
    cQ
    cS
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    eupthp1.v
    eupthp1.i
    eupthp1.f
    eupthp1.a
    eupthp1.b
    eupthp1.c
    eupthp1.d
    eupthp1.p
    eupthp1.n
    eupthp1.e
    eupthp1.x
    eupthp1.u
    eupthp1.h
    eupthp1.q
    eupthp1.s
    eupthp1.l
    eupthp1
    wph
    @0
    wa
    #
    @0
    @1
    wph
    @0
    simpr
    @2
    cH
    cQ
    cS
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
    @0
    @3
    wph
    cQ
    cH
    cS
    eupthistrl
    adantl
    @2
    @4
    cc0
    cP
    cfv
    #
    cC
    @6
    wph
    @4
    @7
    wceq
    #
    @0
    wph
    vk
    cv
    #
    cQ
    cfv
    #
    @9
    cP
    cfv
    #
    wceq
    @8
    vk
    cc0
    cN
    cfz
    co
    #
    cc0
    @9
    cc0
    wceq
    @10
    @4
    @11
    @7
    @9
    cc0
    cQ
    fveq2
    @9
    cc0
    cP
    fveq2
    eqeq12d
    wph
    cB
    cC
    cP
    cQ
    cS
    vk
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    eupthp1.v
    eupthp1.i
    eupthp1.f
    eupthp1.a
    eupthp1.b
    eupthp1.c
    eupthp1.d
    wph
    cF
    cP
    cG
    ceupth
    cfv
    wbr
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    eupthp1.p
    cP
    cF
    cG
    eupthiswlk
    #
    syl
    #
    eupthp1.n
    eupthp1.e
    eupthp1.x
    cS
    ciedg
    cfv
    cI
    cB
    cE
    cop
    csn
    cun
    wceq
    wph
    eupthp1.u
    a1i
    eupthp1.h
    eupthp1.q
    cS
    cvtx
    cfv
    cV
    wceq
    wph
    eupthp1.s
    a1i
    wlkp1lem5
    wph
    @13
    cF
    cI
    cdm
    #
    cword
    wcel
    #
    cc0
    @12
    wcel
    #
    eupthp1.p
    @13
    @14
    @18
    @15
    cP
    cF
    cG
    cI
    eupthp1.i
    wlkf
    #
    syl
    #
    @18
    cF
    chash
    cfv
    #
    cn0
    wcel
    #
    @19
    @17
    cF
    lencl
    @23
    cN
    cn0
    wcel
    @19
    cN
    @22
    cn0
    eupthp1.n
    eleq1i
    cN
    0elfz
    sylbir
    syl
    3syl
    rspcdva
    adantr
    wph
    @7
    cC
    wceq
    @0
    wph
    cC
    @7
    eupth2eucrct.c
    eqcomd
    adantr
    @2
    @6
    cN
    c1
    caddc
    co
    #
    cP
    @24
    cC
    cop
    csn
    cun
    #
    cfv
    #
    cC
    @2
    @5
    @24
    cQ
    @25
    cQ
    @25
    wceq
    @2
    eupthp1.q
    a1i
    @2
    @5
    cF
    cN
    cB
    cop
    #
    csn
    #
    cun
    #
    chash
    cfv
    #
    @22
    @28
    chash
    cfv
    #
    caddc
    co
    #
    @24
    @5
    @30
    wceq
    @2
    cH
    @29
    chash
    eupthp1.h
    fveq2i
    a1i
    @2
    cF
    cfn
    wcel
    #
    @28
    cfn
    wcel
    #
    cF
    @28
    cin
    c0
    wceq
    #
    @30
    @32
    wceq
    wph
    @33
    @0
    wph
    @13
    @14
    @33
    eupthp1.p
    @15
    @14
    @18
    @33
    @20
    @17
    cF
    wrdfin
    syl
    3syl
    adantr
    @34
    @2
    @27
    snfi
    a1i
    @2
    @27
    cF
    wcel
    #
    wn
    #
    @35
    wph
    @37
    @0
    wph
    cF
    cdm
    #
    cc0
    @22
    cfzo
    co
    #
    wceq
    #
    @37
    wph
    @13
    @18
    @40
    eupthp1.p
    @21
    @17
    cF
    wrddm
    3syl
    wph
    @40
    cN
    @38
    wcel
    #
    @36
    wph
    @41
    wn
    @40
    cN
    @39
    wcel
    #
    wn
    wph
    @22
    @39
    wcel
    #
    @42
    @43
    wn
    wph
    cc0
    @22
    fzonel
    a1i
    cN
    @22
    @39
    eupthp1.n
    eleq1i
    sylnibr
    @40
    @41
    @42
    @38
    @39
    cN
    eleq2
    notbid
    syl5ibrcom
    wph
    cN
    cB
    cF
    cvv
    cvv
    cN
    cvv
    wcel
    wph
    cN
    @22
    cvv
    eupthp1.n
    cF
    chash
    fvex
    eqeltri
    a1i
    eupthp1.b
    opeldmd
    nsyld
    mpd
    adantr
    cF
    @27
    disjsn
    sylibr
    cF
    @28
    hashun
    syl3anc
    @32
    @24
    wceq
    @2
    @22
    cN
    @31
    c1
    caddc
    cN
    @22
    eupthp1.n
    eqcomi
    @27
    cvv
    wcel
    @31
    c1
    wceq
    cN
    cB
    opex
    @27
    cvv
    hashsng
    ax-mp
    oveq12i
    a1i
    3eqtrd
    fveq12d
    @2
    @24
    cvv
    wcel
    #
    cC
    cV
    wcel
    #
    @24
    cP
    cdm
    wcel
    wn
    #
    w3a
    #
    @26
    cC
    wceq
    wph
    @47
    @0
    wph
    @44
    @45
    @46
    wph
    cN
    c1
    caddc
    ovexd
    eupthp1.c
    wph
    cB
    cC
    cP
    cF
    cG
    cI
    cN
    cV
    eupthp1.v
    eupthp1.i
    eupthp1.f
    eupthp1.a
    eupthp1.b
    eupthp1.c
    eupthp1.d
    @16
    eupthp1.n
    wlkp1lem1
    3jca
    adantr
    cP
    cvv
    cV
    @24
    cC
    fsnunfv
    syl
    eqtr2d
    3eqtrd
    cQ
    cH
    cS
    iscrct
    sylanbrc
    jca
    mpdan
end
