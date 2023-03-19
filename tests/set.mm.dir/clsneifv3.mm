include "cpw.mm"
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
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "clsneinex.mm"
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
include "clsneiel2.mm"
include "con2bid.mm"
include "rabbidva.mm"
include "3eqtr3a.mm"

theorem clsneifv3
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
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
  let cX: class X
  let vs: setvar s
  let vp: setvar p
  let vl: setvar l
  assume clsnei.o: |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |-> ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) )
  assume clsnei.p: |- P = ( n e. _V |-> ( p e. ( ~P n ^m ~P n ) |-> ( o e. ~P n |-> ( n \ ( p ` ( n \ o ) ) ) ) ) )
  assume clsnei.d: |- D = ( P ` B )
  assume clsnei.f: |- F = ( ~P B O B )
  assume clsnei.h: |- H = ( F o. D )
  assume clsnei.r: |- ( ph -> K H N )
  assume clsneifv.x: |- ( ph -> X e. B )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B l
  disjoint B m
  disjoint B s
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint i s
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint j s
  disjoint k l
  disjoint k m
  disjoint k s
  disjoint l m
  disjoint l s
  disjoint m s
  disjoint B n
  disjoint B o
  disjoint B p
  disjoint n o
  disjoint n p
  disjoint n s
  disjoint o p
  disjoint o s
  disjoint p s
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
  disjoint K n
  disjoint K o
  disjoint K p
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint N l
  disjoint N s
  disjoint N n
  disjoint N o
  disjoint N p
  disjoint X l
  disjoint X m
  disjoint X s
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint ph s
  disjoint n ph
  disjoint o ph
  disjoint p ph
  assert |- ( ph -> ( N ` X ) = { s e. ~P B | -. X e. ( K ` ( B \ s ) ) } )

  proof
    wph
    cB
    cpw
    #
    cX
    cN
    cfv
    #
    cin
    #
    vs
    cv
    #
    @1
    wcel
    #
    vs
    @0
    crab
    @1
    cX
    cB
    @3
    cdif
    cK
    cfv
    wcel
    #
    wn
    #
    vs
    @0
    crab
    vs
    @0
    @1
    dfin5
    wph
    @1
    @0
    wss
    @2
    @1
    wceq
    wph
    @1
    @0
    wph
    cB
    @0
    cpw
    #
    cX
    cN
    wph
    cN
    @7
    cB
    cmap
    co
    wcel
    cB
    @7
    cN
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
    clsneinex
    cN
    @7
    cB
    elmapi
    syl
    clsneifv.x
    ffvelrnd
    elpwid
    @1
    @0
    sseqin2
    sylib
    wph
    @4
    @6
    vs
    @0
    wph
    @3
    @0
    wcel
    #
    wa
    #
    @5
    @4
    @9
    cB
    cD
    cP
    @3
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
    cX
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
    @8
    clsnei.r
    adantr
    wph
    cX
    cB
    wcel
    @8
    clsneifv.x
    adantr
    wph
    @8
    simpr
    clsneiel2
    con2bid
    rabbidva
    3eqtr3a
end
