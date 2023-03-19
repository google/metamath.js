include "wor.mm"
include "cid.mm"
include "cres.mm"
include "cple.mm"
include "cfv.mm"
include "wss.mm"
include "ctos.mm"
include "wcel.mm"
include "wa.mm"
include "opsrtos.mm"
include "eqid.mm"
include "tosso.mm"
include "ibi.mm"
include "syl.mm"
include "simpld.mm"

theorem opsrso
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cT: class T
  let cI: class I
  let c.le: class .<_
  let cO: class O
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  let cC: class C
  let vh: setvar h
  let cD: class D
  let c.lt: class .<
  let wps: wff ps
  assume opsrso.o: |- O = ( ( I ordPwSer R ) ` T )
  assume opsrso.i: |- ( ph -> I e. V )
  assume opsrso.r: |- ( ph -> R e. Toset )
  assume opsrso.t: |- ( ph -> T C_ ( I X. I ) )
  assume opsrso.w: |- ( ph -> T We I )
  assume opsrso.l: |- .<_ = ( lt ` O )
  assume opsrso.b: |- B = ( Base ` O )


  assert |- ( ph -> .<_ Or B )

  proof
    wph
    cB
    c.le
    wor
    #
    cid
    cB
    cres
    cO
    cple
    cfv
    #
    wss
    #
    wph
    cO
    ctos
    wcel
    #
    @0
    @2
    wa
    #
    wph
    cR
    cT
    cI
    cO
    cV
    opsrso.o
    opsrso.i
    opsrso.r
    opsrso.t
    opsrso.w
    opsrtos
    @3
    @4
    cB
    c.le
    cO
    @1
    ctos
    opsrso.b
    @1
    eqid
    opsrso.l
    tosso
    ibi
    syl
    simpld
end
