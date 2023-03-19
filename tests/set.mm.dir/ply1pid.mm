include "cfield.mm"
include "wcel.mm"
include "cidom.mm"
include "clpir.mm"
include "cpid.mm"
include "fldidom.mm"
include "ply1idom.mm"
include "syl.mm"
include "cdr.mm"
include "ccrg.mm"
include "isfld.mm"
include "simplbi.mm"
include "ply1lpir.mm"
include "df-pid.mm"
include "elin2.mm"
include "sylanbrc.mm"

theorem ply1pid
  let cP: class P
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  assume ply1lpir.p: |- P = ( Poly1 ` R )


  assert |- ( R e. Field -> P e. PID )

  proof
    cR
    cfield
    wcel
    #
    cP
    cidom
    wcel
    #
    cP
    clpir
    wcel
    #
    cP
    cpid
    wcel
    @0
    cR
    cidom
    wcel
    @1
    cR
    fldidom
    cP
    cR
    ply1lpir.p
    ply1idom
    syl
    @0
    cR
    cdr
    wcel
    #
    @2
    @0
    @3
    cR
    ccrg
    wcel
    cR
    isfld
    simplbi
    cP
    cR
    ply1lpir.p
    ply1lpir
    syl
    cP
    cidom
    clpir
    cpid
    df-pid
    elin2
    sylanbrc
end
