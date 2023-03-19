include "chlt.mm"
include "wcel.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "4atexlemk.mm"
include "4atexlemp.mm"
include "4atexlems.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"

theorem 4atexlempsb
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
  assume 4thatlempqb.j: |- .\/ = ( join ` K )
  assume 4thatlempqb.a: |- A = ( Atoms ` K )


  assert |- ( ph -> ( P .\/ S ) e. ( Base ` K ) )

  proof
    wph
    cK
    chlt
    wcel
    cP
    cA
    wcel
    cS
    cA
    wcel
    cP
    cS
    c.or
    co
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
    4atexlemk
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
    4atexlemp
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
    4atexlems
    cA
    @0
    c.or
    cK
    cP
    cS
    @0
    eqid
    4thatlempqb.j
    4thatlempqb.a
    hlatjcl
    syl3anc
end
