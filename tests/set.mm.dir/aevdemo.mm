include "weq.mm"
include "wal.mm"
include "wex.mm"
include "wo.mm"
include "wi.mm"
include "aev.mm"
include "19.2d.mm"
include "olcd.mm"
include "aeveq.mm"
include "a1d.mm"
include "alrimiv.mm"
include "syl.mm"
include "jca.mm"

theorem aevdemo
  let vx: setvar x
  let vy: setvar y
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vl: setvar l
  let vm: setvar m
  let vn: setvar n

  disjoint x y
  disjoint h m
  disjoint h n
  disjoint m n
  assert |- ( A. x x = y -> ( ( E. a A. b c = d \/ E. e f = g ) /\ A. h ( i = j -> k = l ) ) )

  proof
    vx
    vy
    weq
    vx
    wal
    #
    vc
    vd
    weq
    vb
    wal
    va
    wex
    #
    vf
    vg
    weq
    #
    ve
    wex
    #
    wo
    vi
    vj
    weq
    #
    vk
    vl
    weq
    #
    wi
    #
    vh
    wal
    #
    @0
    @3
    @1
    @0
    @2
    ve
    vx
    vy
    ve
    vg
    vf
    aev
    19.2d
    olcd
    @0
    vm
    vn
    weq
    vm
    wal
    #
    @7
    vx
    vy
    vm
    vn
    vm
    aev
    @8
    @6
    vh
    @8
    @5
    @4
    vm
    vn
    vk
    vl
    aeveq
    a1d
    alrimiv
    syl
    jca
end
