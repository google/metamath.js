include "wcel.mm"
include "wa.mm"
include "clmod.mm"
include "csca.mm"
include "cfv.mm"
include "cdr.mm"
include "wn.mm"
include "clvec.mm"
include "wnel.mm"
include "cvv.mm"
include "wceq.mm"
include "cnx.mm"
include "cbs.mm"
include "csn.mm"
include "cop.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "tpex.mm"
include "eqeltri.mm"
include "lmodsca.mm"
include "mp1i.mm"
include "cnzr.mm"
include "rng1nnzr.mm"
include "df-nel.mm"
include "sylib.mm"
include "drngnzr.mm"
include "nsyl.mm"
include "adantl.mm"
include "eqneltrrd.mm"
include "intnand.mm"
include "eqid.mm"
include "islvec.mm"
include "xchbinx.mm"
include "sylibr.mm"

theorem lmod1zrnlvec
  let cR: class R
  let cI: class I
  let cM: class M
  let cV: class V
  let cW: class W
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vi: setvar i
  let vp: setvar p
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x
  assume lmod1zr.r: |- R = { <. ( Base ` ndx ) , { Z } >. , <. ( +g ` ndx ) , { <. <. Z , Z >. , Z >. } >. , <. ( .r ` ndx ) , { <. <. Z , Z >. , Z >. } >. }
  assume lmod1zr.m: |- M = ( { <. ( Base ` ndx ) , { I } >. , <. ( +g ` ndx ) , { <. <. I , I >. , I >. } >. , <. ( Scalar ` ndx ) , R >. } u. { <. ( .s ` ndx ) , { <. <. Z , I >. , I >. } >. } )


  assert |- ( ( I e. V /\ Z e. W ) -> M e/ LVec )

  proof
    cI
    cV
    wcel
    #
    cZ
    cW
    wcel
    #
    wa
    #
    cM
    clmod
    wcel
    #
    cM
    csca
    cfv
    #
    cdr
    wcel
    #
    wa
    #
    wn
    cM
    clvec
    wnel
    #
    @2
    @5
    @3
    @2
    cR
    @4
    cdr
    cR
    cvv
    wcel
    cR
    @4
    wceq
    @2
    cR
    cnx
    cbs
    cfv
    cZ
    csn
    cop
    #
    cnx
    cplusg
    cfv
    cZ
    cZ
    cop
    cZ
    cop
    csn
    #
    cop
    #
    cnx
    cmulr
    cfv
    @9
    cop
    #
    ctp
    cvv
    lmod1zr.r
    @8
    @10
    @11
    tpex
    eqeltri
    cI
    csn
    cI
    cI
    cop
    cI
    cop
    csn
    cZ
    cI
    cop
    cI
    cop
    csn
    cR
    cM
    cvv
    lmod1zr.m
    lmodsca
    mp1i
    @1
    cR
    cdr
    wcel
    #
    wn
    @0
    @1
    cR
    cnzr
    wcel
    #
    @12
    @1
    cR
    cnzr
    wnel
    @13
    wn
    cR
    cW
    cZ
    lmod1zr.r
    rng1nnzr
    cR
    cnzr
    df-nel
    sylib
    cR
    drngnzr
    nsyl
    adantl
    eqneltrrd
    intnand
    @7
    cM
    clvec
    wcel
    @6
    cM
    clvec
    df-nel
    @4
    cM
    @4
    eqid
    islvec
    xchbinx
    sylibr
end
