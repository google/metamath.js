include "csn.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "wss.mm"
include "dih0rn.mm"
include "syl.mm"
include "dihrnss.mm"
include "syl2anc.mm"
include "djhcom.mm"
include "djh01.mm"
include "eqtrd.mm"

theorem djh02
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume djh01.h: |- H = ( LHyp ` K )
  assume djh01.u: |- U = ( ( DVecH ` K ) ` W )
  assume djh01.o: |- .0. = ( 0g ` U )
  assume djh01.i: |- I = ( ( DIsoH ` K ) ` W )
  assume djh01.j: |- .\/ = ( ( joinH ` K ) ` W )
  assume djh01.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume djh01.x: |- ( ph -> X e. ran I )


  assert |- ( ph -> ( { .0. } .\/ X ) = X )

  proof
    wph
    c.0
    csn
    #
    cX
    c.or
    co
    cX
    @0
    c.or
    co
    cX
    wph
    cU
    cH
    c.or
    cK
    cU
    cbs
    cfv
    #
    cW
    @0
    cX
    djh01.h
    djh01.u
    @1
    eqid
    #
    djh01.j
    djh01.k
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @0
    cI
    crn
    #
    wcel
    #
    @0
    @1
    wss
    djh01.k
    wph
    @3
    @5
    djh01.k
    cU
    cH
    cI
    cK
    cW
    c.0
    djh01.h
    djh01.i
    djh01.u
    djh01.o
    dih0rn
    syl
    cU
    cH
    cI
    cK
    @1
    cW
    @0
    djh01.h
    djh01.u
    djh01.i
    @2
    dihrnss
    syl2anc
    wph
    @3
    cX
    @4
    wcel
    cX
    @1
    wss
    djh01.k
    djh01.x
    cU
    cH
    cI
    cK
    @1
    cW
    cX
    djh01.h
    djh01.u
    djh01.i
    @2
    dihrnss
    syl2anc
    djhcom
    wph
    cU
    cH
    cI
    c.or
    cK
    cW
    cX
    c.0
    djh01.h
    djh01.u
    djh01.o
    djh01.i
    djh01.j
    djh01.k
    djh01.x
    djh01
    eqtrd
end
