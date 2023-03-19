include "cfv.mm"
include "wbr.mm"
include "w3a.mm"
include "wcel.mm"
include "cdif.mm"
include "wn.mm"
include "wb.mm"
include "cvv.mm"
include "neicvgbex.mm"
include "wa.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wf1o.mm"
include "wfn.mm"
include "simpr.mm"
include "pwexg.mm"
include "syl.mm"
include "fsovf1od.mm"
include "f1ofn.mm"
include "wf.mm"
include "dssmapf1od.mm"
include "f1of.mm"
include "fsovfd.mm"
include "ccom.mm"
include "breqi.mm"
include "sylib.mm"
include "adantr.mm"
include "brcofffn.mm"
include "mpdan.mm"
include "simpr2.mm"
include "ntrclselnel1.mm"
include "eqid.mm"
include "simpr1.mm"
include "ccnv.mm"
include "a1i.mm"
include "wrel.mm"
include "id.mm"
include "f1orel.mm"
include "relbrcnvg.mm"
include "3syl.mm"
include "fsovcnvd.mm"
include "breqd.mm"
include "3bitr2d.mm"
include "mpbid.mm"
include "ntrneiel.mm"
include "simpr3.mm"
include "difssd.mm"
include "sselpwd.mm"
include "notbid.mm"
include "3bitr3d.mm"

theorem neicvgel1
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
  assert |- ( ph -> ( S e. ( N ` X ) <-> -. ( B \ S ) e. ( M ` X ) ) )

  proof
    wph
    cN
    cN
    cG
    cfv
    #
    cG
    wbr
    #
    @0
    @0
    cD
    cfv
    #
    cD
    wbr
    #
    @2
    cM
    cF
    wbr
    #
    w3a
    #
    cS
    cX
    cN
    cfv
    wcel
    #
    cB
    cS
    cdif
    #
    cX
    cM
    cfv
    wcel
    #
    wn
    #
    wb
    wph
    cB
    cvv
    wcel
    #
    @5
    wph
    cB
    cD
    cP
    cF
    cG
    cH
    cM
    cN
    neicvg.d
    neicvg.h
    neicvg.r
    neicvgbex
    #
    wph
    @10
    wa
    #
    cN
    cM
    cF
    cD
    cG
    cB
    cpw
    #
    cpw
    cB
    cmap
    co
    #
    @13
    @13
    cmap
    co
    #
    @15
    @12
    @15
    @14
    cF
    wf1o
    cF
    @15
    wfn
    @12
    vm
    vl
    @13
    cB
    vk
    cF
    cO
    cvv
    cvv
    vi
    vj
    neicvg.o
    @12
    @10
    @13
    cvv
    wcel
    wph
    @10
    simpr
    #
    cB
    cvv
    pwexg
    #
    syl
    #
    @16
    neicvg.f
    fsovf1od
    @15
    @14
    cF
    f1ofn
    syl
    @12
    @15
    @15
    cD
    wf1o
    @15
    @15
    cD
    wf
    @12
    cB
    cD
    vp
    cP
    cvv
    vo
    vn
    neicvg.p
    neicvg.d
    @16
    dssmapf1od
    @15
    @15
    cD
    f1of
    syl
    @12
    vm
    vl
    cB
    @13
    vk
    cG
    cO
    cvv
    cvv
    vi
    vj
    neicvg.o
    @16
    @18
    neicvg.g
    fsovfd
    wph
    cN
    cM
    cF
    cD
    cG
    ccom
    ccom
    #
    wbr
    #
    @10
    wph
    cN
    cM
    cH
    wbr
    @20
    neicvg.r
    cN
    cM
    cH
    @19
    neicvg.h
    breqi
    sylib
    adantr
    brcofffn
    mpdan
    wph
    @5
    wa
    #
    cX
    cS
    @0
    cfv
    wcel
    cX
    @7
    @2
    cfv
    wcel
    #
    wn
    @6
    @9
    @21
    cB
    cD
    cS
    vn
    vo
    vp
    @0
    @2
    cP
    cX
    neicvg.p
    neicvg.d
    wph
    @1
    @3
    @4
    simpr2
    wph
    cX
    cB
    wcel
    @5
    neicvgel.x
    adantr
    #
    wph
    cS
    @13
    wcel
    @5
    neicvgel.s
    adantr
    #
    ntrclselnel1
    @21
    cB
    cS
    vi
    vj
    vk
    vm
    @13
    cB
    cO
    co
    #
    @0
    cN
    cO
    cX
    vl
    neicvg.o
    @25
    eqid
    #
    @21
    @1
    @0
    cN
    @25
    wbr
    #
    wph
    @1
    @3
    @4
    simpr1
    @21
    @1
    cN
    @0
    cB
    @13
    cO
    co
    #
    wbr
    #
    @0
    cN
    @28
    ccnv
    #
    wbr
    #
    @27
    @1
    @29
    wb
    @21
    cN
    @0
    cG
    @28
    neicvg.g
    breqi
    a1i
    @21
    @14
    @15
    @28
    wf1o
    #
    @28
    wrel
    @31
    @29
    wb
    @21
    @10
    @32
    wph
    @10
    @5
    @11
    adantr
    #
    @10
    vm
    vl
    cB
    @13
    vk
    @28
    cO
    cvv
    cvv
    vi
    vj
    neicvg.o
    @10
    id
    #
    @17
    @28
    eqid
    #
    fsovf1od
    syl
    @14
    @15
    @28
    f1orel
    @0
    cN
    @28
    relbrcnvg
    3syl
    @21
    @10
    @31
    @27
    wb
    @33
    @10
    @30
    @25
    @0
    cN
    @10
    vm
    vl
    cB
    @13
    vk
    @28
    @25
    cO
    cvv
    cvv
    vi
    vj
    neicvg.o
    @34
    @17
    @35
    @26
    fsovcnvd
    breqd
    syl
    3bitr2d
    mpbid
    @23
    @24
    ntrneiel
    @21
    @22
    @8
    @21
    cB
    @7
    vi
    vj
    vk
    vm
    cF
    @2
    cM
    cO
    cX
    vl
    neicvg.o
    neicvg.f
    wph
    @1
    @3
    @4
    simpr3
    @23
    wph
    @7
    @13
    wcel
    @5
    wph
    @7
    cB
    cvv
    @11
    wph
    cB
    cS
    difssd
    sselpwd
    adantr
    ntrneiel
    notbid
    3bitr3d
    mpdan
end
