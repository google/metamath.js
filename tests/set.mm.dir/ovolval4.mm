include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cop.mm"
include "cmpt.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "ifbieq12d.mm"
include "opeq12d.mm"
include "cbvmptv.mm"
include "ovolval4lem2.mm"

theorem ovolval4
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let cM: class M
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  assume ovolval4.a: |- ( ph -> A C_ RR )
  assume ovolval4.m: |- M = { y e. RR* | E. f e. ( ( RR X. RR ) ^m NN ) ( A C_ U. ran ( (,) o. f ) /\ y = ( sum^ ` ( ( vol o. (,) ) o. f ) ) ) }

  disjoint A f
  disjoint A y
  disjoint f y
  disjoint ph y
  disjoint f k
  disjoint f n
  disjoint k n
  disjoint k x
  assert |- ( ph -> ( vol* ` A ) = inf ( M , RR* , < ) )

  proof
    wph
    vy
    cA
    vf
    vn
    vk
    cn
    vk
    cv
    #
    vf
    cv
    #
    cfv
    #
    c1st
    cfv
    #
    @3
    @2
    c2nd
    cfv
    #
    cle
    wbr
    #
    @4
    @3
    cif
    #
    cop
    #
    cmpt
    cM
    ovolval4.a
    ovolval4.m
    vk
    vn
    cn
    @7
    vn
    cv
    #
    @1
    cfv
    #
    c1st
    cfv
    #
    @10
    @9
    c2nd
    cfv
    #
    cle
    wbr
    #
    @11
    @10
    cif
    #
    cop
    @0
    @8
    wceq
    #
    @3
    @10
    @6
    @13
    @14
    @2
    @9
    c1st
    @0
    @8
    @1
    fveq2
    #
    fveq2d
    #
    @14
    @5
    @12
    @4
    @3
    @11
    @10
    @14
    @3
    @10
    @4
    @11
    cle
    @16
    @14
    @2
    @9
    c2nd
    @15
    fveq2d
    #
    breq12d
    @17
    @16
    ifbieq12d
    opeq12d
    cbvmptv
    ovolval4lem2
end
