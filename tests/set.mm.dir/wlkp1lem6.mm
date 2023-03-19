include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "ciedg.mm"
include "w3a.mm"
include "cc0.mm"
include "cfzo.mm"
include "wcel.mm"
include "cfz.mm"
include "wral.mm"
include "wlkp1lem5.mm"
include "wa.mm"
include "wi.mm"
include "elfzofz.mm"
include "adantl.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "syl.mm"
include "imp.mm"
include "fzofzp1.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "adantr.mm"
include "fveq1i.mm"
include "wne.mm"
include "wn.mm"
include "fzonel.mm"
include "eleq1.mm"
include "mtbii.mm"
include "a1i.mm"
include "con2d.mm"
include "neqned.mm"
include "fvunsn.mm"
include "syl5eq.mm"
include "fveq12d.mm"
include "cdm.mm"
include "chash.mm"
include "oveq2i.mm"
include "eleq2i.mm"
include "cword.mm"
include "cwlks.mm"
include "wbr.mm"
include "wlkf.mm"
include "wrdsymbcl.mm"
include "ex.mm"
include "syl5bi.mm"
include "syl5ibrcom.mm"
include "con3d.mm"
include "mpid.mm"
include "eqtrd.mm"
include "3jca.mm"
include "mpidan.mm"
include "ralrimiva.mm"

theorem wlkp1lem6
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cS: class S
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  let vx: setvar x
  assume wlkp1.v: |- V = ( Vtx ` G )
  assume wlkp1.i: |- I = ( iEdg ` G )
  assume wlkp1.f: |- ( ph -> Fun I )
  assume wlkp1.a: |- ( ph -> I e. Fin )
  assume wlkp1.b: |- ( ph -> B e. _V )
  assume wlkp1.c: |- ( ph -> C e. V )
  assume wlkp1.d: |- ( ph -> -. B e. dom I )
  assume wlkp1.w: |- ( ph -> F ( Walks ` G ) P )
  assume wlkp1.n: |- N = ( # ` F )
  assume wlkp1.e: |- ( ph -> E e. ( Edg ` G ) )
  assume wlkp1.x: |- ( ph -> { ( P ` N ) , C } C_ E )
  assume wlkp1.u: |- ( ph -> ( iEdg ` S ) = ( I u. { <. B , E >. } ) )
  assume wlkp1.h: |- H = ( F u. { <. N , B >. } )
  assume wlkp1.q: |- Q = ( P u. { <. ( N + 1 ) , C >. } )
  assume wlkp1.s: |- ( ph -> ( Vtx ` S ) = V )

  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint N x
  disjoint P x
  disjoint Q x
  assert |- ( ph -> A. k e. ( 0 ..^ N ) ( ( Q ` k ) = ( P ` k ) /\ ( Q ` ( k + 1 ) ) = ( P ` ( k + 1 ) ) /\ ( ( iEdg ` S ) ` ( H ` k ) ) = ( I ` ( F ` k ) ) ) )

  proof
    wph
    vk
    cv
    #
    cQ
    cfv
    #
    @0
    cP
    cfv
    #
    wceq
    #
    @0
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    @4
    cP
    cfv
    #
    wceq
    #
    @0
    cH
    cfv
    #
    cS
    ciedg
    cfv
    #
    cfv
    #
    @0
    cF
    cfv
    #
    cI
    cfv
    #
    wceq
    #
    w3a
    #
    vk
    cc0
    cN
    cfzo
    co
    #
    wph
    @0
    @15
    wcel
    #
    vx
    cv
    #
    cQ
    cfv
    #
    @17
    cP
    cfv
    #
    wceq
    #
    vx
    cc0
    cN
    cfz
    co
    #
    wral
    #
    @14
    wph
    cB
    cC
    cP
    cQ
    cS
    vx
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    wlkp1.v
    wlkp1.i
    wlkp1.f
    wlkp1.a
    wlkp1.b
    wlkp1.c
    wlkp1.d
    wlkp1.w
    wlkp1.n
    wlkp1.e
    wlkp1.x
    wlkp1.u
    wlkp1.h
    wlkp1.q
    wlkp1.s
    wlkp1lem5
    wph
    @16
    wa
    #
    @22
    wa
    @3
    @7
    @13
    @23
    @22
    @3
    @23
    @0
    @21
    wcel
    #
    @22
    @3
    wi
    @16
    @24
    wph
    @0
    cc0
    cN
    elfzofz
    adantl
    @20
    @3
    vx
    @0
    @21
    @17
    @0
    wceq
    @18
    @1
    @19
    @2
    @17
    @0
    cQ
    fveq2
    @17
    @0
    cP
    fveq2
    eqeq12d
    rspcv
    syl
    imp
    @23
    @22
    @7
    @23
    @4
    @21
    wcel
    #
    @22
    @7
    wi
    @16
    @25
    wph
    cc0
    cN
    @0
    fzofzp1
    adantl
    @20
    @7
    vx
    @4
    @21
    @17
    @4
    wceq
    @18
    @5
    @19
    @6
    @17
    @4
    cQ
    fveq2
    @17
    @4
    cP
    fveq2
    eqeq12d
    rspcv
    syl
    imp
    @23
    @13
    @22
    @23
    @10
    @11
    cI
    cB
    cE
    cop
    csn
    cun
    #
    cfv
    #
    @12
    @23
    @8
    @11
    @9
    @26
    wph
    @9
    @26
    wceq
    @16
    wlkp1.u
    adantr
    @23
    @8
    @0
    cF
    cN
    cB
    cop
    csn
    cun
    #
    cfv
    #
    @11
    @0
    cH
    @28
    wlkp1.h
    fveq1i
    @23
    cN
    @0
    wne
    @29
    @11
    wceq
    @23
    cN
    @0
    wph
    @16
    cN
    @0
    wceq
    #
    wn
    wph
    @30
    @16
    @30
    @16
    wn
    wi
    wph
    @30
    cN
    @15
    wcel
    @16
    cc0
    cN
    fzonel
    cN
    @0
    @15
    eleq1
    mtbii
    a1i
    con2d
    imp
    neqned
    cF
    cN
    cB
    @0
    fvunsn
    syl
    syl5eq
    fveq12d
    @23
    cB
    @11
    wne
    @27
    @12
    wceq
    @23
    cB
    @11
    wph
    @16
    cB
    @11
    wceq
    #
    wn
    #
    wph
    @16
    cB
    cI
    cdm
    #
    wcel
    #
    wn
    #
    @32
    wlkp1.d
    wph
    @16
    @35
    @32
    wi
    @23
    @31
    @34
    @23
    @34
    @31
    @11
    @33
    wcel
    #
    wph
    @16
    @36
    @16
    @0
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    wcel
    #
    wph
    @36
    @15
    @38
    @0
    cN
    @37
    cc0
    cfzo
    wlkp1.n
    oveq2i
    eleq2i
    wph
    cF
    @33
    cword
    wcel
    #
    @39
    @36
    wi
    wph
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    @40
    wlkp1.w
    cP
    cF
    cG
    cI
    wlkp1.i
    wlkf
    syl
    @40
    @39
    @36
    @0
    @33
    cF
    wrdsymbcl
    ex
    syl
    syl5bi
    imp
    cB
    @11
    @33
    eleq1
    syl5ibrcom
    con3d
    ex
    mpid
    imp
    neqned
    cI
    cB
    cE
    @11
    fvunsn
    syl
    eqtrd
    adantr
    3jca
    mpidan
    ralrimiva
end
