include "ccgrg.mm"
include "cfv.mm"
include "cds.mm"
include "eqid.mm"
include "cgr3id.mm"
include "hlid.mm"
include "necomd.mm"
include "iscgrad.mm"

theorem cgraid
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cG: class G
  let cI: class I
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  assume cgraid.p: |- P = ( Base ` G )
  assume cgraid.i: |- I = ( Itv ` G )
  assume cgraid.g: |- ( ph -> G e. TarskiG )
  assume cgraid.k: |- K = ( hlG ` G )
  assume cgraid.a: |- ( ph -> A e. P )
  assume cgraid.b: |- ( ph -> B e. P )
  assume cgraid.c: |- ( ph -> C e. P )
  assume cgraid.1: |- ( ph -> A =/= B )
  assume cgraid.2: |- ( ph -> B =/= C )


  assert |- ( ph -> <" A B C "> ( cgrA ` G ) <" A B C "> )

  proof
    wph
    cA
    cB
    cC
    cA
    cP
    cB
    cC
    cG
    cI
    cK
    cA
    cC
    cgraid.p
    cgraid.i
    cgraid.k
    cgraid.g
    cgraid.a
    cgraid.b
    cgraid.c
    cgraid.a
    cgraid.b
    cgraid.c
    cgraid.a
    cgraid.c
    wph
    cA
    cB
    cC
    cP
    cG
    ccgrg
    cfv
    #
    cG
    cI
    cG
    cds
    cfv
    #
    cgraid.p
    @1
    eqid
    cgraid.i
    @0
    eqid
    cgraid.g
    cgraid.a
    cgraid.b
    cgraid.c
    cgr3id
    wph
    cA
    cA
    cB
    cP
    cG
    cI
    cK
    cgraid.p
    cgraid.i
    cgraid.k
    cgraid.a
    cgraid.a
    cgraid.b
    cgraid.g
    cgraid.1
    hlid
    wph
    cC
    cA
    cB
    cP
    cG
    cI
    cK
    cgraid.p
    cgraid.i
    cgraid.k
    cgraid.c
    cgraid.a
    cgraid.b
    cgraid.g
    wph
    cB
    cC
    cgraid.2
    necomd
    hlid
    iscgrad
end
