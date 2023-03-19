include "ctrl.mm"
include "cfv.mm"
include "clss.mm"
include "cltrn.mm"
include "cmee.mm"
include "clspn.mm"
include "eqid.mm"
include "dia2dimlem13.mm"

theorem dia2dim
  let wph: wff ph
  let cA: class A
  let c.po: class .(+)
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cY: class Y
  assume dia2dim.l: |- .<_ = ( le ` K )
  assume dia2dim.j: |- .\/ = ( join ` K )
  assume dia2dim.a: |- A = ( Atoms ` K )
  assume dia2dim.h: |- H = ( LHyp ` K )
  assume dia2dim.y: |- Y = ( ( DVecA ` K ) ` W )
  assume dia2dim.pl: |- .(+) = ( LSSum ` Y )
  assume dia2dim.i: |- I = ( ( DIsoA ` K ) ` W )
  assume dia2dim.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dia2dim.u: |- ( ph -> ( U e. A /\ U .<_ W ) )
  assume dia2dim.v: |- ( ph -> ( V e. A /\ V .<_ W ) )


  assert |- ( ph -> ( I ` ( U .\/ V ) ) C_ ( ( I ` U ) .(+) ( I ` V ) ) )

  proof
    wph
    cA
    c.po
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cY
    clss
    cfv
    #
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cU
    cH
    cI
    c.or
    cK
    c.le
    cK
    cmee
    cfv
    #
    cY
    clspn
    cfv
    #
    cV
    cW
    cY
    dia2dim.l
    dia2dim.j
    @3
    eqid
    dia2dim.a
    dia2dim.h
    @2
    eqid
    @0
    eqid
    dia2dim.y
    @1
    eqid
    dia2dim.pl
    @4
    eqid
    dia2dim.i
    dia2dim.k
    dia2dim.u
    dia2dim.v
    dia2dimlem13
end
