include "cnv.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "nvzcl.mm"
include "cc0.mm"
include "nvz0.mm"
include "0le1.mm"
include "syl6eqbr.mm"
include "eqid.mm"
include "jctir.mm"
include "fveq2.mm"
include "breq1d.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "fvex.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elab.mm"
include "sylibr.mm"

theorem nmosetn0
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  let cU: class U
  let cM: class M
  let cN: class N
  let cX: class X
  let cZ: class Z
  assume nmosetn0.1: |- X = ( BaseSet ` U )
  assume nmosetn0.5: |- Z = ( 0vec ` U )
  assume nmosetn0.4: |- M = ( normCV ` U )

  disjoint x y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint T x
  disjoint T y
  disjoint X x
  disjoint X y
  disjoint Z x
  disjoint Z y
  assert |- ( U e. NrmCVec -> ( N ` ( T ` Z ) ) e. { x | E. y e. X ( ( M ` y ) <_ 1 /\ x = ( N ` ( T ` y ) ) ) } )

  proof
    cU
    cnv
    wcel
    #
    vy
    cv
    #
    cM
    cfv
    #
    c1
    cle
    wbr
    #
    cZ
    cT
    cfv
    #
    cN
    cfv
    #
    @1
    cT
    cfv
    #
    cN
    cfv
    #
    wceq
    #
    wa
    #
    vy
    cX
    wrex
    #
    @5
    @3
    vx
    cv
    #
    @7
    wceq
    #
    wa
    #
    vy
    cX
    wrex
    #
    vx
    cab
    wcel
    @0
    cZ
    cX
    wcel
    cZ
    cM
    cfv
    #
    c1
    cle
    wbr
    #
    @5
    @5
    wceq
    #
    wa
    #
    @10
    cU
    cX
    cZ
    nmosetn0.1
    nmosetn0.5
    nvzcl
    @0
    @16
    @17
    @0
    @15
    cc0
    c1
    cle
    cU
    cM
    cZ
    nmosetn0.5
    nmosetn0.4
    nvz0
    0le1
    syl6eqbr
    @5
    eqid
    jctir
    @9
    @18
    vy
    cZ
    cX
    @1
    cZ
    wceq
    #
    @3
    @16
    @8
    @17
    @19
    @2
    @15
    c1
    cle
    @1
    cZ
    cM
    fveq2
    breq1d
    @19
    @7
    @5
    @5
    @19
    @6
    @4
    cN
    @1
    cZ
    cT
    fveq2
    fveq2d
    eqeq2d
    anbi12d
    rspcev
    syl2anc
    @14
    @10
    vx
    @5
    @4
    cN
    fvex
    @11
    @5
    wceq
    #
    @13
    @9
    vy
    cX
    @20
    @12
    @8
    @3
    @11
    @5
    @7
    eqeq1
    anbi2d
    rexbidv
    elab
    sylibr
end
