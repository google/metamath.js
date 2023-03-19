include "chlt.mm"
include "wcel.mm"
include "clc.mm"
include "4atexlemk.mm"
include "hlcvl.mm"
include "syl.mm"

theorem 4atexlemkc
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


  assert |- ( ph -> K e. CvLat )

  proof
    wph
    cK
    chlt
    wcel
    cK
    clc
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
    4atexlemk
    cK
    hlcvl
    syl
end
