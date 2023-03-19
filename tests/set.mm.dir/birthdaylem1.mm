include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "cn.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "wf1.mm"
include "cab.mm"
include "wf.mm"
include "f1f.mm"
include "ss2abi.mm"
include "3sstr4i.mm"
include "cmap.mm"
include "wceq.mm"
include "fzfi.mm"
include "mapvalg.mm"
include "mp2an.mm"
include "eqtr4i.mm"
include "mapfi.mm"
include "eqeltri.mm"
include "elfz1end.mm"
include "ne0i.mm"
include "sylbi.mm"
include "eqeq1i.mm"
include "ovex.mm"
include "map0.mm"
include "simplbi.mm"
include "necon3i.mm"
include "syl.mm"
include "3pm3.2i.mm"

theorem birthdaylem1
  let cS: class S
  let cT: class T
  let vf: setvar f
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  assume birthday.s: |- S = { f | f : ( 1 ... K ) --> ( 1 ... N ) }
  assume birthday.t: |- T = { f | f : ( 1 ... K ) -1-1-> ( 1 ... N ) }

  disjoint K f
  disjoint N f
  disjoint f k
  disjoint f n
  disjoint k n
  disjoint K k
  disjoint K n
  disjoint N k
  disjoint N n
  assert |- ( T C_ S /\ S e. Fin /\ ( N e. NN -> S =/= (/) ) )

  proof
    cT
    cS
    wss
    cS
    cfn
    wcel
    cN
    cn
    wcel
    #
    cS
    c0
    wne
    #
    wi
    c1
    cK
    cfz
    co
    #
    c1
    cN
    cfz
    co
    #
    vf
    cv
    #
    wf1
    #
    vf
    cab
    @2
    @3
    @4
    wf
    #
    vf
    cab
    #
    cT
    cS
    @5
    @6
    vf
    @2
    @3
    @4
    f1f
    ss2abi
    birthday.t
    birthday.s
    3sstr4i
    cS
    @3
    @2
    cmap
    co
    #
    cfn
    cS
    @7
    @8
    birthday.s
    @3
    cfn
    wcel
    #
    @2
    cfn
    wcel
    #
    @8
    @7
    wceq
    c1
    cN
    fzfi
    #
    c1
    cK
    fzfi
    #
    @3
    @2
    cfn
    cfn
    vf
    mapvalg
    mp2an
    eqtr4i
    #
    @9
    @10
    @8
    cfn
    wcel
    @11
    @12
    @3
    @2
    mapfi
    mp2an
    eqeltri
    @0
    @3
    c0
    wne
    #
    @1
    @0
    cN
    @3
    wcel
    @14
    cN
    elfz1end
    @3
    cN
    ne0i
    sylbi
    cS
    c0
    @3
    c0
    cS
    c0
    wceq
    @8
    c0
    wceq
    #
    @3
    c0
    wceq
    #
    cS
    @8
    c0
    @13
    eqeq1i
    @15
    @16
    @2
    c0
    wne
    @3
    @2
    c1
    cN
    cfz
    ovex
    c1
    cK
    cfz
    ovex
    map0
    simplbi
    sylbi
    necon3i
    syl
    3pm3.2i
end
