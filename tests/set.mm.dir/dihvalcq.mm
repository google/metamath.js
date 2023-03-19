include "clss.mm"
include "cfv.mm"
include "eqid.mm"
include "dihvalcqpre.mm"

theorem dihvalcq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.po: class .(+)
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  assume dihvalcq.b: |- B = ( Base ` K )
  assume dihvalcq.l: |- .<_ = ( le ` K )
  assume dihvalcq.j: |- .\/ = ( join ` K )
  assume dihvalcq.m: |- ./\ = ( meet ` K )
  assume dihvalcq.a: |- A = ( Atoms ` K )
  assume dihvalcq.h: |- H = ( LHyp ` K )
  assume dihvalcq.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihvalcq.d: |- D = ( ( DIsoB ` K ) ` W )
  assume dihvalcq.c: |- C = ( ( DIsoC ` K ) ` W )
  assume dihvalcq.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihvalcq.p: |- .(+) = ( LSSum ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( Q .\/ ( X ./\ W ) ) = X ) ) -> ( I ` X ) = ( ( C ` Q ) .(+) ( D ` ( X ./\ W ) ) ) )

  proof
    cA
    cB
    cC
    cD
    c.po
    cQ
    cU
    clss
    cfv
    #
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    cX
    dihvalcq.b
    dihvalcq.l
    dihvalcq.j
    dihvalcq.m
    dihvalcq.a
    dihvalcq.h
    dihvalcq.i
    dihvalcq.d
    dihvalcq.c
    dihvalcq.u
    @0
    eqid
    dihvalcq.p
    dihvalcqpre
end
