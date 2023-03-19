include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "4atexlemw.mm"
include "eqid.mm"
include "lhpbase.mm"
include "syl.mm"

theorem 4atexlemwb
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  assume 4thatlem.ph: |- ( ph <-> ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( S e. A /\ ( R e. A /\ -. R .<_ W /\ ( P .\/ R ) = ( Q .\/ R ) ) /\ ( T e. A /\ ( U .\/ T ) = ( V .\/ T ) ) ) /\ ( P =/= Q /\ -. S .<_ ( P .\/ Q ) ) ) )
  assume 4thatlemmwb.h: |- H = ( LHyp ` K )


  assert |- ( ph -> W e. ( Base ` K ) )

  proof
    wph
    cW
    cH
    wcel
    cW
    cK
    cbs
    cfv
    #
    wcel
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    cV
    cW
    4thatlem.ph
    4atexlemw
    @0
    cH
    cK
    cW
    @0
    eqid
    4thatlemmwb.h
    lhpbase
    syl
end
