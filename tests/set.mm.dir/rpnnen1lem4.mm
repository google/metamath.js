include "cv.mm"
include "cr.mm"
include "wcel.mm"
include "cfv.mm"
include "crn.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "clt.mm"
include "csup.mm"
include "cn.mm"
include "cq.mm"
include "wf.mm"
include "cmap.mm"
include "co.mm"
include "rpnnen1lem1.mm"
include "elmap.mm"
include "sylib.mm"
include "frn.mm"
include "qssre.mm"
include "syl6ss.mm"
include "syl.mm"
include "cdm.mm"
include "c1.mm"
include "1nn.mm"
include "ne0ii.mm"
include "fdm.mm"
include "neeq1d.mm"
include "mpbiri.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "rpnnen1lem3.mm"
include "weq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "mpdan.mm"
include "suprcl.mm"
include "syl3anc.mm"

theorem rpnnen1lem4
  let vx: setvar x
  let cT: class T
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let vy: setvar y
  assume rpnnen1lem.1: |- T = { n e. ZZ | ( n / k ) < x }
  assume rpnnen1lem.2: |- F = ( x e. RR |-> ( k e. NN |-> ( sup ( T , RR , < ) / k ) ) )
  assume rpnnen1lem.n: |- NN e. _V
  assume rpnnen1lem.q: |- QQ e. _V

  disjoint F k
  disjoint F n
  disjoint F x
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint T n
  disjoint F y
  disjoint k y
  disjoint n y
  disjoint x y
  disjoint T y
  assert |- ( x e. RR -> sup ( ran ( F ` x ) , RR , < ) e. RR )

  proof
    vx
    cv
    #
    cr
    wcel
    #
    @0
    cF
    cfv
    #
    crn
    #
    cr
    wss
    #
    @3
    c0
    wne
    #
    vn
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vn
    @3
    wral
    #
    vy
    cr
    wrex
    #
    @3
    cr
    clt
    csup
    cr
    wcel
    @1
    cn
    cq
    @2
    wf
    #
    @4
    @1
    @2
    cq
    cn
    cmap
    co
    wcel
    @11
    vx
    cT
    vk
    vn
    cF
    rpnnen1lem.1
    rpnnen1lem.2
    rpnnen1lem.n
    rpnnen1lem.q
    rpnnen1lem1
    cq
    cn
    @2
    rpnnen1lem.q
    rpnnen1lem.n
    elmap
    sylib
    #
    @11
    @3
    cq
    cr
    cn
    cq
    @2
    frn
    qssre
    syl6ss
    syl
    @1
    @11
    @5
    @12
    @11
    @2
    cdm
    #
    c0
    wne
    #
    @5
    @11
    @14
    cn
    c0
    wne
    c1
    cn
    1nn
    ne0ii
    @11
    @13
    cn
    c0
    cn
    cq
    @2
    fdm
    neeq1d
    mpbiri
    @13
    c0
    @3
    c0
    @2
    dm0rn0
    necon3bii
    sylib
    syl
    @1
    @6
    @0
    cle
    wbr
    #
    vn
    @3
    wral
    #
    @10
    vx
    cT
    vk
    vn
    cF
    rpnnen1lem.1
    rpnnen1lem.2
    rpnnen1lem.n
    rpnnen1lem.q
    rpnnen1lem3
    @9
    @16
    vy
    @0
    cr
    vy
    vx
    weq
    @8
    @15
    vn
    @3
    @7
    @0
    @6
    cle
    breq2
    ralbidv
    rspcev
    mpdan
    vy
    vn
    @3
    suprcl
    syl3anc
end
