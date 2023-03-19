include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "wf.mm"
include "wa.mm"
include "cvv.mm"
include "w3a.mm"
include "cwlks.mm"
include "wbr.mm"
include "eqid.mm"
include "wlkf.mm"
include "wlkp.mm"
include "jca.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "elfvexd.mm"
include "adantr.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "simprl.mm"
include "snex.mm"
include "unexg.mm"
include "sylancl.mm"
include "syl5eqel.mm"
include "c1.mm"
include "caddc.mm"
include "cpm.mm"
include "ovex.mm"
include "fvex.mm"
include "fpm.mm"
include "ad2antll.mm"
include "3jca.mm"
include "mpdan.mm"

theorem wlkp1lem4
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


  assert |- ( ph -> ( S e. _V /\ H e. _V /\ Q e. _V ) )

  proof
    wph
    cF
    cG
    ciedg
    cfv
    #
    cdm
    cword
    #
    wcel
    #
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    #
    cG
    cvtx
    cfv
    #
    cP
    wf
    #
    wa
    #
    cS
    cvv
    wcel
    #
    cH
    cvv
    wcel
    #
    cQ
    cvv
    wcel
    #
    w3a
    wph
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @7
    wlkp1.w
    @11
    @2
    @6
    cP
    cF
    cG
    @0
    @0
    eqid
    wlkf
    cP
    cF
    cG
    @5
    @5
    eqid
    wlkp
    jca
    syl
    wph
    @7
    wa
    #
    @8
    @9
    @10
    wph
    @8
    @7
    wph
    cC
    cvtx
    cS
    wph
    cC
    cV
    cS
    cvtx
    cfv
    wlkp1.c
    wlkp1.s
    eleqtrrd
    elfvexd
    adantr
    @12
    cH
    cF
    cN
    cB
    cop
    #
    csn
    #
    cun
    #
    cvv
    wlkp1.h
    @12
    @2
    @14
    cvv
    wcel
    @15
    cvv
    wcel
    wph
    @2
    @6
    simprl
    @13
    snex
    cF
    @14
    @1
    cvv
    unexg
    sylancl
    syl5eqel
    @12
    cQ
    cP
    cN
    c1
    caddc
    co
    cC
    cop
    #
    csn
    #
    cun
    #
    cvv
    wlkp1.q
    @12
    cP
    @5
    @4
    cpm
    co
    #
    wcel
    #
    @17
    cvv
    wcel
    @18
    cvv
    wcel
    @6
    @20
    wph
    @2
    @4
    @5
    cP
    cc0
    @3
    cfz
    ovex
    cG
    cvtx
    fvex
    fpm
    ad2antll
    @16
    snex
    cP
    @17
    @19
    cvv
    unexg
    sylancl
    syl5eqel
    3jca
    mpdan
end
