include "cnzr.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cbs.mm"
include "c0g.mm"
include "wne.mm"
include "cco1.mm"
include "cur.mm"
include "crg.mm"
include "ply1nz.mm"
include "nzrring.mm"
include "eqid.mm"
include "ringidcl.mm"
include "3syl.mm"
include "nzrnz.mm"
include "syl.mm"
include "cn0.mm"
include "cv.mm"
include "cif.mm"
include "cmpt.mm"
include "cascl.mm"
include "ply1scl1.mm"
include "fveq2d.mm"
include "coe1scl.mm"
include "syl2anc.mm"
include "eqtr3d.mm"
include "deg1scl.mm"
include "syl3anc.mm"
include "fveq12d.mm"
include "0nn0.mm"
include "iftrue.mm"
include "fvex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "ismon1p.mm"
include "syl3anbrc.mm"
include "jca.mm"

theorem mon1pid
  let cD: class D
  let cP: class P
  let cR: class R
  let c.1: class .1.
  let cM: class M
  let vx: setvar x
  assume mon1pid.p: |- P = ( Poly1 ` R )
  assume mon1pid.o: |- .1. = ( 1r ` P )
  assume mon1pid.m: |- M = ( Monic1p ` R )
  assume mon1pid.d: |- D = ( deg1 ` R )


  assert |- ( R e. NzRing -> ( .1. e. M /\ ( D ` .1. ) = 0 ) )

  proof
    cR
    cnzr
    wcel
    #
    c.1
    cM
    wcel
    #
    c.1
    cD
    cfv
    #
    cc0
    wceq
    @0
    c.1
    cP
    cbs
    cfv
    #
    wcel
    #
    c.1
    cP
    c0g
    cfv
    #
    wne
    #
    @2
    c.1
    cco1
    cfv
    #
    cfv
    #
    cR
    cur
    cfv
    #
    wceq
    @1
    @0
    cP
    cnzr
    wcel
    #
    cP
    crg
    wcel
    @4
    cP
    cR
    mon1pid.p
    ply1nz
    #
    cP
    nzrring
    @3
    cP
    c.1
    @3
    eqid
    #
    mon1pid.o
    ringidcl
    3syl
    @0
    @10
    @6
    @11
    cP
    c.1
    @5
    mon1pid.o
    @5
    eqid
    #
    nzrnz
    syl
    @0
    @8
    cc0
    vx
    cn0
    vx
    cv
    cc0
    wceq
    #
    @9
    cR
    c0g
    cfv
    #
    cif
    #
    cmpt
    #
    cfv
    #
    @9
    @0
    @2
    cc0
    @7
    @17
    @0
    @9
    cP
    cascl
    cfv
    #
    cfv
    #
    cco1
    cfv
    #
    @7
    @17
    @0
    @20
    c.1
    cco1
    @0
    cR
    crg
    wcel
    #
    @20
    c.1
    wceq
    cR
    nzrring
    #
    @19
    cP
    cR
    @9
    c.1
    mon1pid.p
    @19
    eqid
    #
    @9
    eqid
    #
    mon1pid.o
    ply1scl1
    syl
    #
    fveq2d
    @0
    @22
    @9
    cR
    cbs
    cfv
    #
    wcel
    #
    @21
    @17
    wceq
    @23
    @0
    @22
    @28
    @23
    @27
    cR
    @9
    @27
    eqid
    #
    @25
    ringidcl
    syl
    #
    vx
    @19
    cP
    cR
    @27
    @9
    @15
    mon1pid.p
    @24
    @29
    @15
    eqid
    #
    coe1scl
    syl2anc
    eqtr3d
    @0
    @20
    cD
    cfv
    #
    @2
    cc0
    @0
    @20
    c.1
    cD
    @26
    fveq2d
    @0
    @22
    @28
    @9
    @15
    wne
    @32
    cc0
    wceq
    @23
    @30
    cR
    @9
    @15
    @25
    @31
    nzrnz
    @19
    cD
    cP
    cR
    @9
    @27
    @15
    mon1pid.d
    mon1pid.p
    @29
    @24
    @31
    deg1scl
    syl3anc
    eqtr3d
    #
    fveq12d
    cc0
    cn0
    wcel
    @18
    @9
    wceq
    0nn0
    vx
    cc0
    @16
    @9
    cn0
    @17
    @14
    @9
    @15
    iftrue
    @17
    eqid
    cR
    cur
    fvex
    fvmpt
    ax-mp
    syl6eq
    @3
    cD
    cP
    cR
    @9
    c.1
    cM
    @5
    mon1pid.p
    @12
    @13
    mon1pid.d
    mon1pid.m
    @25
    ismon1p
    syl3anbrc
    @33
    jca
end
