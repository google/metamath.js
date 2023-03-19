include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wbr.mm"
include "cdif.mm"
include "wn.mm"
include "wb.mm"
include "clsneibex.mm"
include "ancli.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "simpr.mm"
include "pwexg.mm"
include "syl.mm"
include "fsovfd.mm"
include "ffnd.mm"
include "wf1o.mm"
include "wf.mm"
include "dssmapf1od.mm"
include "f1of.mm"
include "ccom.mm"
include "breqi.mm"
include "sylib.mm"
include "adantr.mm"
include "brcoffn.mm"
include "simprl.mm"
include "ad2antrr.mm"
include "ntrclselnel1.mm"
include "simprr.mm"
include "simplr.mm"
include "difssd.mm"
include "sselpwd.mm"
include "ntrneiel.mm"
include "notbid.mm"
include "bitrd.mm"
include "3syl.mm"

theorem clsneiel1
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
  let cH: class H
  let cK: class K
  let cN: class N
  let cO: class O
  let cX: class X
  let vp: setvar p
  let vl: setvar l
  assume clsnei.o: |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |-> ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) )
  assume clsnei.p: |- P = ( n e. _V |-> ( p e. ( ~P n ^m ~P n ) |-> ( o e. ~P n |-> ( n \ ( p ` ( n \ o ) ) ) ) ) )
  assume clsnei.d: |- D = ( P ` B )
  assume clsnei.f: |- F = ( ~P B O B )
  assume clsnei.h: |- H = ( F o. D )
  assume clsnei.r: |- ( ph -> K H N )
  assume clsneiel.x: |- ( ph -> X e. B )
  assume clsneiel.s: |- ( ph -> S e. ~P B )

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
  assert |- ( ph -> ( X e. ( K ` S ) <-> -. ( B \ S ) e. ( N ` X ) ) )

  proof
    wph
    wph
    cB
    cvv
    wcel
    #
    wa
    #
    @1
    cK
    cK
    cD
    cfv
    #
    cD
    wbr
    #
    @2
    cN
    cF
    wbr
    #
    wa
    #
    wa
    #
    cX
    cS
    cK
    cfv
    wcel
    #
    cB
    cS
    cdif
    #
    cX
    cN
    cfv
    wcel
    #
    wn
    #
    wb
    wph
    @0
    wph
    cB
    cD
    cP
    cF
    cH
    cK
    cN
    clsnei.d
    clsnei.h
    clsnei.r
    clsneibex
    ancli
    @1
    @5
    @1
    cK
    cN
    cF
    cD
    cB
    cpw
    #
    @11
    cmap
    co
    #
    @12
    @1
    @12
    @11
    cpw
    cB
    cmap
    co
    cF
    @1
    vm
    vl
    @11
    cB
    vk
    cF
    cO
    cvv
    cvv
    vi
    vj
    clsnei.o
    @1
    @0
    @11
    cvv
    wcel
    wph
    @0
    simpr
    #
    cB
    cvv
    pwexg
    syl
    @13
    clsnei.f
    fsovfd
    ffnd
    @1
    @12
    @12
    cD
    wf1o
    @12
    @12
    cD
    wf
    @1
    cB
    cD
    vp
    cP
    cvv
    vo
    vn
    clsnei.p
    clsnei.d
    @13
    dssmapf1od
    @12
    @12
    cD
    f1of
    syl
    wph
    cK
    cN
    cF
    cD
    ccom
    #
    wbr
    #
    @0
    wph
    cK
    cN
    cH
    wbr
    @15
    clsnei.r
    cK
    cN
    cH
    @14
    clsnei.h
    breqi
    sylib
    adantr
    brcoffn
    ancli
    @6
    @7
    cX
    @8
    @2
    cfv
    wcel
    #
    wn
    @10
    @6
    cB
    cD
    cS
    vn
    vo
    vp
    cK
    @2
    cP
    cX
    clsnei.p
    clsnei.d
    @1
    @3
    @4
    simprl
    wph
    cX
    cB
    wcel
    @0
    @5
    clsneiel.x
    ad2antrr
    #
    wph
    cS
    @11
    wcel
    @0
    @5
    clsneiel.s
    ad2antrr
    ntrclselnel1
    @6
    @16
    @9
    @6
    cB
    @8
    vi
    vj
    vk
    vm
    cF
    @2
    cN
    cO
    cX
    vl
    clsnei.o
    clsnei.f
    @1
    @3
    @4
    simprr
    @17
    @6
    @8
    cB
    cvv
    wph
    @0
    @5
    simplr
    @6
    cB
    cS
    difssd
    sselpwd
    ntrneiel
    notbid
    bitrd
    3syl
end
