include "wcel.mm"
include "cfrmd.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "cpr.mm"
include "cv.mm"
include "cword.mm"
include "cconcat.mm"
include "cxp.mm"
include "cres.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-frmd.mm"
include "a1i.mm"
include "wa.mm"
include "wrdeq.mm"
include "eqcomd.mm"
include "sylan9eqr.mm"
include "opeq2d.mm"
include "sqxpeqd.mm"
include "reseq2d.mm"
include "syl6eqr.mm"
include "preq12d.mm"
include "elex.mm"
include "prex.mm"
include "fvmptd.mm"
include "syl5eq.mm"

theorem frmdval
  let cB: class B
  let c.pl: class .+
  let cI: class I
  let cM: class M
  let cV: class V
  let vi: setvar i
  assume frmdval.m: |- M = ( freeMnd ` I )
  assume frmdval.b: |- ( I e. V -> B = Word I )
  assume frmdval.p: |- .+ = ( ++ |` ( B X. B ) )


  assert |- ( I e. V -> M = { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. } )

  proof
    cI
    cV
    wcel
    #
    cM
    cI
    cfrmd
    cfv
    cnx
    cbs
    cfv
    #
    cB
    cop
    #
    cnx
    cplusg
    cfv
    #
    c.pl
    cop
    #
    cpr
    #
    frmdval.m
    @0
    vi
    cI
    @1
    vi
    cv
    #
    cword
    #
    cop
    #
    @3
    cconcat
    @7
    @7
    cxp
    #
    cres
    #
    cop
    #
    cpr
    #
    @5
    cvv
    cfrmd
    cvv
    cfrmd
    vi
    cvv
    @12
    cmpt
    wceq
    @0
    vi
    df-frmd
    a1i
    @0
    @6
    cI
    wceq
    #
    wa
    #
    @8
    @2
    @11
    @4
    @14
    @7
    cB
    @1
    @13
    @0
    @7
    cI
    cword
    #
    cB
    @6
    cI
    wrdeq
    @0
    cB
    @15
    frmdval.b
    eqcomd
    sylan9eqr
    #
    opeq2d
    @14
    @10
    c.pl
    @3
    @14
    @10
    cconcat
    cB
    cB
    cxp
    #
    cres
    c.pl
    @14
    @9
    @17
    cconcat
    @14
    @7
    cB
    @16
    sqxpeqd
    reseq2d
    frmdval.p
    syl6eqr
    opeq2d
    preq12d
    cI
    cV
    elex
    @5
    cvv
    wcel
    @0
    @2
    @4
    prex
    a1i
    fvmptd
    syl5eq
end
