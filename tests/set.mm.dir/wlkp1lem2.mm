include "chash.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "fveq2i.mm"
include "a1i.mm"
include "cvv.mm"
include "wcel.mm"
include "cfn.mm"
include "wn.mm"
include "wa.mm"
include "opex.mm"
include "cwlks.mm"
include "wbr.mm"
include "cdm.mm"
include "cword.mm"
include "wlkf.mm"
include "wrdfin.mm"
include "3syl.mm"
include "cc0.mm"
include "cfzo.mm"
include "wi.mm"
include "fzonel.mm"
include "eleq1.mm"
include "notbid.mm"
include "syl5ibr.mm"
include "ax-mp.mm"
include "wfn.mm"
include "wrdfn.mm"
include "fnop.mm"
include "ex.mm"
include "syl.mm"
include "mtod.mm"
include "jca.mm"
include "hashunsng.mm"
include "mpsyl.mm"
include "eqcomi.mm"
include "oveq1d.mm"
include "3eqtrd.mm"

theorem wlkp1lem2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
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


  assert |- ( ph -> ( # ` H ) = ( N + 1 ) )

  proof
    wph
    cH
    chash
    cfv
    #
    cF
    cN
    cB
    cop
    #
    csn
    cun
    #
    chash
    cfv
    #
    cF
    chash
    cfv
    #
    c1
    caddc
    co
    #
    cN
    c1
    caddc
    co
    @0
    @3
    wceq
    wph
    cH
    @2
    chash
    wlkp1.h
    fveq2i
    a1i
    @1
    cvv
    wcel
    wph
    cF
    cfn
    wcel
    #
    @1
    cF
    wcel
    #
    wn
    #
    wa
    @3
    @5
    wceq
    cN
    cB
    opex
    wph
    @6
    @8
    wph
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cF
    cI
    cdm
    #
    cword
    wcel
    #
    @6
    wlkp1.w
    cP
    cF
    cG
    cI
    wlkp1.i
    wlkf
    #
    @10
    cF
    wrdfin
    3syl
    wph
    @7
    cN
    cc0
    @4
    cfzo
    co
    #
    wcel
    #
    cN
    @4
    wceq
    #
    wph
    @14
    wn
    #
    wi
    wlkp1.n
    wph
    @16
    @15
    @4
    @13
    wcel
    #
    wn
    #
    @18
    wph
    cc0
    @4
    fzonel
    a1i
    @15
    @14
    @17
    cN
    @4
    @13
    eleq1
    notbid
    syl5ibr
    ax-mp
    wph
    cF
    @13
    wfn
    #
    @7
    @14
    wi
    wph
    @9
    @11
    @19
    wlkp1.w
    @12
    @10
    cF
    wrdfn
    3syl
    @19
    @7
    @14
    @13
    cN
    cB
    cF
    fnop
    ex
    syl
    mtod
    jca
    cF
    @1
    cvv
    hashunsng
    mpsyl
    wph
    @4
    cN
    c1
    caddc
    @4
    cN
    wceq
    wph
    cN
    @4
    wlkp1.n
    eqcomi
    a1i
    oveq1d
    3eqtrd
end
