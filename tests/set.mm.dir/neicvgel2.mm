include "cdif.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "neicvgrcomplex.mm"
include "neicvgel1.mm"
include "wss.mm"
include "wceq.mm"
include "elpwid.mm"
include "dfss4.mm"
include "sylib.mm"
include "eleq1d.mm"
include "notbid.mm"
include "bitrd.mm"

theorem neicvgel2
  let wph: wff ph
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
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let cO: class O
  let cX: class X
  let vp: setvar p
  let vl: setvar l
  assume neicvg.o: |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |-> ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) )
  assume neicvg.p: |- P = ( n e. _V |-> ( p e. ( ~P n ^m ~P n ) |-> ( o e. ~P n |-> ( n \ ( p ` ( n \ o ) ) ) ) ) )
  assume neicvg.d: |- D = ( P ` B )
  assume neicvg.f: |- F = ( ~P B O B )
  assume neicvg.g: |- G = ( B O ~P B )
  assume neicvg.h: |- H = ( F o. ( D o. G ) )
  assume neicvg.r: |- ( ph -> N H M )
  assume neicvgel.x: |- ( ph -> X e. B )
  assume neicvgel.s: |- ( ph -> S e. ~P B )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B l
  disjoint B m
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint k l
  disjoint k m
  disjoint l m
  disjoint B n
  disjoint B o
  disjoint B p
  disjoint n o
  disjoint n p
  disjoint o p
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
  disjoint G i
  disjoint G j
  disjoint G k
  disjoint G l
  disjoint G m
  disjoint G n
  disjoint G o
  disjoint G p
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint M l
  disjoint M n
  disjoint M o
  disjoint M p
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint N l
  disjoint N m
  disjoint N n
  disjoint N o
  disjoint N p
  disjoint S m
  disjoint S o
  disjoint X l
  disjoint X m
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint n ph
  disjoint o ph
  disjoint p ph
  assert |- ( ph -> ( ( B \ S ) e. ( N ` X ) <-> -. S e. ( M ` X ) ) )

  proof
    wph
    cB
    cS
    cdif
    #
    cX
    cN
    cfv
    wcel
    cB
    @0
    cdif
    #
    cX
    cM
    cfv
    #
    wcel
    #
    wn
    cS
    @2
    wcel
    #
    wn
    wph
    cB
    cD
    cP
    @0
    vi
    vj
    vk
    vm
    vn
    vo
    cF
    cG
    cH
    cM
    cN
    cO
    cX
    vp
    vl
    neicvg.o
    neicvg.p
    neicvg.d
    neicvg.f
    neicvg.g
    neicvg.h
    neicvg.r
    neicvgel.x
    wph
    cB
    cD
    cP
    cS
    cF
    cG
    cH
    cM
    cN
    neicvg.d
    neicvg.h
    neicvg.r
    neicvgrcomplex
    neicvgel1
    wph
    @3
    @4
    wph
    @1
    cS
    @2
    wph
    cS
    cB
    wss
    @1
    cS
    wceq
    wph
    cS
    cB
    neicvgel.s
    elpwid
    cS
    cB
    dfss4
    sylib
    eleq1d
    notbid
    bitrd
end
