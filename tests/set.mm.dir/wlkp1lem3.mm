include "cfv.mm"
include "ciedg.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "a1i.mm"
include "fveq1d.mm"
include "cvv.mm"
include "wcel.mm"
include "cdm.mm"
include "wn.mm"
include "chash.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cwlks.mm"
include "wbr.mm"
include "cword.mm"
include "wlkf.mm"
include "cn0.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "lencl.mm"
include "wrddm.mm"
include "wa.mm"
include "fzonel.mm"
include "simpr.mm"
include "eleq12d.mm"
include "mtbiri.mm"
include "syl2anc.mm"
include "3syl.mm"
include "fsnunfv.mm"
include "mp3an2i.mm"
include "eqtrd.mm"
include "fveq12d.mm"

theorem wlkp1lem3
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


  assert |- ( ph -> ( ( iEdg ` S ) ` ( H ` N ) ) = ( ( I u. { <. B , E >. } ) ` B ) )

  proof
    wph
    cN
    cH
    cfv
    #
    cB
    cS
    ciedg
    cfv
    cI
    cB
    cE
    cop
    csn
    cun
    wlkp1.u
    wph
    @0
    cN
    cF
    cN
    cB
    cop
    csn
    cun
    #
    cfv
    #
    cB
    wph
    cN
    cH
    @1
    cH
    @1
    wceq
    wph
    wlkp1.h
    a1i
    fveq1d
    cN
    cvv
    wcel
    wph
    cB
    cvv
    wcel
    cN
    cF
    cdm
    #
    wcel
    #
    wn
    #
    @2
    cB
    wceq
    cN
    cF
    chash
    cfv
    #
    cvv
    wlkp1.n
    cF
    chash
    fvex
    eqeltri
    wlkp1.b
    wph
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    cF
    cI
    cdm
    #
    cword
    wcel
    #
    @5
    wlkp1.w
    cP
    cF
    cG
    cI
    wlkp1.i
    wlkf
    @8
    @6
    cn0
    wcel
    #
    @3
    cc0
    @6
    cfzo
    co
    #
    wceq
    #
    @5
    @7
    cF
    lencl
    @7
    cF
    wrddm
    @9
    @11
    wa
    #
    @4
    @6
    @10
    wcel
    cc0
    @6
    fzonel
    @12
    cN
    @6
    @3
    @10
    cN
    @6
    wceq
    @12
    wlkp1.n
    a1i
    @9
    @11
    simpr
    eleq12d
    mtbiri
    syl2anc
    3syl
    cF
    cvv
    cvv
    cN
    cB
    fsnunfv
    mp3an2i
    eqtrd
    fveq12d
end
