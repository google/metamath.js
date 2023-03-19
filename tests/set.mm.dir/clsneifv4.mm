include "cfv.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "crab.mm"
include "cdif.mm"
include "wn.mm"
include "dfin5.mm"
include "wss.mm"
include "wceq.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "clsneikex.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "sseqin2.mm"
include "sylib.mm"
include "wa.mm"
include "wbr.mm"
include "adantr.mm"
include "simpr.mm"
include "clsneiel1.mm"
include "rabbidva.mm"
include "3eqtr3a.mm"

theorem clsneifv4
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cD: class D
  let cP: class P
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let cF: class F
  let cH: class H
  let cK: class K
  let cN: class N
  let cO: class O
  let vp: setvar p
  let vl: setvar l
  assume clsnei.o: |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |-> ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) )
  assume clsnei.p: |- P = ( n e. _V |-> ( p e. ( ~P n ^m ~P n ) |-> ( o e. ~P n |-> ( n \ ( p ` ( n \ o ) ) ) ) ) )
  assume clsnei.d: |- D = ( P ` B )
  assume clsnei.f: |- F = ( ~P B O B )
  assume clsnei.h: |- H = ( F o. D )
  assume clsnei.r: |- ( ph -> K H N )
  assume clsneifv.s: |- ( ph -> S e. ~P B )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B l
  disjoint B m
  disjoint B x
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint i x
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint j x
  disjoint k l
  disjoint k m
  disjoint k x
  disjoint l m
  disjoint l x
  disjoint m x
  disjoint B n
  disjoint B o
  disjoint B p
  disjoint n o
  disjoint n p
  disjoint n x
  disjoint o p
  disjoint o x
  disjoint p x
  disjoint D i
  disjoint D j
  disjoint D k
  disjoint D l
  disjoint D m
  disjoint D n
  disjoint D o
  disjoint D p
  disjoint F i
  disjoint F j
  disjoint F k
  disjoint F l
  disjoint F n
  disjoint F o
  disjoint F p
  disjoint K i
  disjoint K j
  disjoint K k
  disjoint K l
  disjoint K m
  disjoint K x
  disjoint K n
  disjoint K o
  disjoint K p
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint N l
  disjoint N n
  disjoint N o
  disjoint N p
  disjoint S m
  disjoint S x
  disjoint S o
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint ph x
  disjoint n ph
  disjoint o ph
  disjoint p ph
  assert |- ( ph -> ( K ` S ) = { x e. B | -. ( B \ S ) e. ( N ` x ) } )

  proof
    wph
    cB
    cS
    cK
    cfv
    #
    cin
    #
    vx
    cv
    #
    @0
    wcel
    #
    vx
    cB
    crab
    @0
    cB
    cS
    cdif
    @2
    cN
    cfv
    wcel
    wn
    #
    vx
    cB
    crab
    vx
    cB
    @0
    dfin5
    wph
    @0
    cB
    wss
    @1
    @0
    wceq
    wph
    @0
    cB
    wph
    cB
    cpw
    #
    @5
    cS
    cK
    wph
    cK
    @5
    @5
    cmap
    co
    wcel
    @5
    @5
    cK
    wf
    wph
    cB
    cD
    cP
    vi
    vj
    vk
    vm
    vn
    vo
    cF
    cH
    cK
    cN
    cO
    vp
    vl
    clsnei.o
    clsnei.p
    clsnei.d
    clsnei.f
    clsnei.h
    clsnei.r
    clsneikex
    cK
    @5
    @5
    elmapi
    syl
    clsneifv.s
    ffvelrnd
    elpwid
    @0
    cB
    sseqin2
    sylib
    wph
    @3
    @4
    vx
    cB
    wph
    @2
    cB
    wcel
    #
    wa
    cB
    cD
    cP
    cS
    vi
    vj
    vk
    vm
    vn
    vo
    cF
    cH
    cK
    cN
    cO
    @2
    vp
    vl
    clsnei.o
    clsnei.p
    clsnei.d
    clsnei.f
    clsnei.h
    wph
    cK
    cN
    cH
    wbr
    @6
    clsnei.r
    adantr
    wph
    @6
    simpr
    wph
    cS
    @5
    wcel
    @6
    clsneifv.s
    adantr
    clsneiel1
    rabbidva
    3eqtr3a
end
