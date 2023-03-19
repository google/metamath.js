include "hb.mm"
include "tor.mm"
include "kbr.mm"
include "tal.mm"
include "tv.mm"
include "tim.mm"
include "kl.mm"
include "kc.mm"
include "kt.mm"
include "wor.mm"
include "wov.mm"
include "df-or.mm"
include "oveq.mm"
include "ht.mm"
include "wal.mm"
include "wim.mm"
include "wv.mm"
include "wl.mm"
include "wc.mm"
include "ke.mm"
include "weqi.mm"
include "id.mm"
include "oveq1.mm"
include "leq.mm"
include "ceq2.mm"
include "oveq2.mm"
include "ovl.mm"
include "eqtri.mm"

theorem orval
  let vx: var x
  let ta: term A
  let tb: term B
  let vf: var f
  let vp: var p
  let vq: var q
  assume imval.1: |- A : bool
  assume imval.2: |- B : bool

  disjoint A x
  disjoint B x
  disjoint f p
  disjoint f q
  disjoint f x
  disjoint A f
  disjoint p q
  disjoint p x
  disjoint A p
  disjoint q x
  disjoint A q
  disjoint B f
  disjoint B q
  assert |- T. |= [ [ A \/ B ] = ( ! \ x : bool . [ [ A ==> x : bool ] ==> [ [ B ==> x : bool ] ==> x : bool ] ] ) ]

  proof
    hb
    ta
    tb
    tor
    kbr
    ta
    tb
    hb
    vp
    hb
    vq
    tal
    hb
    vx
    hb
    vp
    tv
    #
    hb
    vx
    tv
    #
    tim
    kbr
    #
    hb
    vq
    tv
    #
    @1
    tim
    kbr
    #
    @1
    tim
    kbr
    #
    tim
    kbr
    #
    kl
    #
    kc
    #
    kl
    kl
    #
    kbr
    tal
    hb
    vx
    ta
    @1
    tim
    kbr
    #
    tb
    @1
    tim
    kbr
    #
    @1
    tim
    kbr
    #
    tim
    kbr
    #
    kl
    #
    kc
    #
    kt
    hb
    hb
    hb
    ta
    tb
    tor
    wor
    imval.1
    imval.2
    wov
    hb
    hb
    hb
    ta
    tb
    tor
    kt
    @9
    wor
    imval.1
    imval.2
    vx
    vp
    vq
    df-or
    oveq
    hb
    hb
    hb
    vp
    vq
    @8
    tal
    hb
    vx
    @10
    @5
    tim
    kbr
    #
    kl
    #
    kc
    @15
    ta
    tb
    hb
    hb
    ht
    #
    hb
    tal
    @7
    hb
    wal
    #
    hb
    hb
    vx
    @6
    hb
    hb
    hb
    @2
    @5
    tim
    wim
    hb
    hb
    hb
    @0
    @1
    tim
    wim
    hb
    vp
    wv
    #
    hb
    vx
    wv
    #
    wov
    #
    hb
    hb
    hb
    @4
    @1
    tim
    wim
    hb
    hb
    hb
    @3
    @1
    tim
    wim
    hb
    vq
    wv
    #
    @21
    wov
    #
    @21
    wov
    #
    wov
    #
    wl
    #
    wc
    imval.1
    imval.2
    @18
    hb
    @7
    @17
    tal
    @0
    ta
    ke
    kbr
    #
    @19
    @27
    hb
    hb
    vx
    @6
    @16
    @28
    @26
    hb
    hb
    hb
    @2
    @5
    @10
    tim
    @28
    wim
    @22
    @25
    hb
    hb
    hb
    @0
    @1
    ta
    tim
    @28
    wim
    @20
    @21
    @28
    hb
    @0
    ta
    @20
    imval.1
    weqi
    id
    oveq1
    oveq1
    leq
    ceq2
    @18
    hb
    @17
    @14
    tal
    @3
    tb
    ke
    kbr
    #
    @19
    hb
    hb
    vx
    @16
    hb
    hb
    hb
    @10
    @5
    tim
    wim
    hb
    hb
    hb
    ta
    @1
    tim
    wim
    imval.1
    @21
    wov
    #
    @25
    wov
    #
    wl
    hb
    hb
    vx
    @16
    @13
    @29
    @31
    hb
    hb
    hb
    @10
    @5
    tim
    @29
    @12
    wim
    @30
    @25
    hb
    hb
    hb
    @4
    @1
    @11
    tim
    @29
    wim
    @24
    @21
    hb
    hb
    hb
    @3
    @1
    tb
    tim
    @29
    wim
    @23
    @21
    @29
    hb
    @3
    tb
    @23
    imval.2
    weqi
    id
    oveq1
    oveq1
    oveq2
    leq
    ceq2
    ovl
    eqtri
end
