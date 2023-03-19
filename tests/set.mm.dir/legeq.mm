include "leg0.mm"
include "legtri3.mm"
include "axtgcgrid.mm"

theorem legeq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let c.le: class .<_
  let c.mi: class .-
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cE: class E
  let cF: class F
  assume legval.p: |- P = ( Base ` G )
  assume legval.d: |- .- = ( dist ` G )
  assume legval.i: |- I = ( Itv ` G )
  assume legval.l: |- .<_ = ( leG ` G )
  assume legval.g: |- ( ph -> G e. TarskiG )
  assume legid.a: |- ( ph -> A e. P )
  assume legid.b: |- ( ph -> B e. P )
  assume legtrd.c: |- ( ph -> C e. P )
  assume legtrd.d: |- ( ph -> D e. P )
  assume legeq.1: |- ( ph -> ( A .- B ) .<_ ( C .- C ) )


  assert |- ( ph -> A = B )

  proof
    wph
    cP
    cG
    cI
    c.mi
    cA
    cB
    cC
    legval.p
    legval.d
    legval.i
    legval.g
    legid.a
    legid.b
    legtrd.c
    wph
    cA
    cB
    cC
    cC
    cP
    cG
    cI
    c.le
    c.mi
    legval.p
    legval.d
    legval.i
    legval.l
    legval.g
    legid.a
    legid.b
    legtrd.c
    legtrd.c
    legeq.1
    wph
    cC
    cA
    cA
    cB
    cP
    cG
    cI
    c.le
    c.mi
    legval.p
    legval.d
    legval.i
    legval.l
    legval.g
    legtrd.c
    legid.a
    legid.a
    legid.b
    leg0
    legtri3
    axtgcgrid
end
