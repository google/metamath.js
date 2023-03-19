include "wcel.mm"
include "c1.mm"
include "cvv.mm"
include "cn0.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "ccom.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cseq.mm"
include "cfv.mm"
include "cif.mm"
include "crelexp.mm"
include "df-relexp.mm"
include "a1i.mm"
include "wa.mm"
include "wne.mm"
include "simprr.mm"
include "ax-1ne0.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "syl.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "simprl.mm"
include "mpteq2dv.mm"
include "seqeq3d.mm"
include "fveq12d.mm"
include "1z.mm"
include "eqidd.mm"
include "1ex.mm"
include "simpl.mm"
include "fvmptd.mm"
include "seq1i.mm"
include "3eqtrd.mm"
include "elex.mm"
include "1nn0.mm"
include "ovmpt2d.mm"

theorem relexp1g
  let cR: class R
  let cV: class V
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( R e. V -> ( R ^r 1 ) = R )

  proof
    cR
    cV
    wcel
    #
    vr
    vn
    cR
    c1
    cvv
    cn0
    vn
    cv
    #
    cc0
    wceq
    #
    cid
    vr
    cv
    #
    cdm
    @3
    crn
    cun
    cres
    #
    @1
    vx
    vy
    cvv
    cvv
    vx
    cv
    @3
    ccom
    cmpt2
    #
    vz
    cvv
    @3
    cmpt
    #
    c1
    cseq
    #
    cfv
    #
    cif
    #
    cR
    crelexp
    cvv
    crelexp
    vr
    vn
    cvv
    cn0
    @9
    cmpt2
    wceq
    @0
    vx
    vy
    vz
    vn
    vr
    df-relexp
    a1i
    @0
    @3
    cR
    wceq
    #
    @1
    c1
    wceq
    #
    wa
    #
    wa
    #
    @9
    @8
    c1
    @5
    vz
    cvv
    cR
    cmpt
    #
    c1
    cseq
    #
    cfv
    cR
    @13
    @2
    @4
    @8
    @13
    @1
    cc0
    @13
    @11
    @1
    cc0
    wne
    #
    @0
    @10
    @11
    simprr
    #
    @11
    @16
    c1
    cc0
    wne
    ax-1ne0
    @1
    c1
    cc0
    neeq1
    mpbiri
    syl
    neneqd
    iffalsed
    @13
    @1
    c1
    @7
    @15
    @13
    @6
    @14
    @5
    c1
    @13
    vz
    cvv
    @3
    cR
    @0
    @10
    @11
    simprl
    mpteq2dv
    seqeq3d
    @17
    fveq12d
    @13
    cR
    @5
    @14
    c1
    1z
    @13
    vz
    c1
    cR
    cR
    cvv
    @14
    cV
    @13
    @14
    eqidd
    @13
    vz
    cv
    c1
    wceq
    wa
    cR
    eqidd
    c1
    cvv
    wcel
    @13
    1ex
    a1i
    @0
    @12
    simpl
    fvmptd
    seq1i
    3eqtrd
    cR
    cV
    elex
    #
    c1
    cn0
    wcel
    @0
    1nn0
    a1i
    @18
    ovmpt2d
end
