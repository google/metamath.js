include "cop.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cco.mm"
include "wceq.mm"
include "eqid.mm"
include "xpcco.mm"
include "ovex.mm"
include "op1std.mm"
include "syl.mm"

theorem xpcco1st
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cK: class K
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume xpcco1st.t: |- T = ( C Xc. D )
  assume xpcco1st.b: |- B = ( Base ` T )
  assume xpcco1st.k: |- K = ( Hom ` T )
  assume xpcco1st.o: |- O = ( comp ` T )
  assume xpcco1st.x: |- ( ph -> X e. B )
  assume xpcco1st.y: |- ( ph -> Y e. B )
  assume xpcco1st.z: |- ( ph -> Z e. B )
  assume xpcco1st.f: |- ( ph -> F e. ( X K Y ) )
  assume xpcco1st.g: |- ( ph -> G e. ( Y K Z ) )
  assume xpcco1st.1: |- .x. = ( comp ` C )


  assert |- ( ph -> ( 1st ` ( G ( <. X , Y >. O Z ) F ) ) = ( ( 1st ` G ) ( <. ( 1st ` X ) , ( 1st ` Y ) >. .x. ( 1st ` Z ) ) ( 1st ` F ) ) )

  proof
    wph
    cG
    cF
    cX
    cY
    cop
    cZ
    cO
    co
    co
    #
    cG
    c1st
    cfv
    #
    cF
    c1st
    cfv
    #
    cX
    c1st
    cfv
    cY
    c1st
    cfv
    cop
    cZ
    c1st
    cfv
    c.x
    co
    #
    co
    #
    cG
    c2nd
    cfv
    #
    cF
    c2nd
    cfv
    #
    cX
    c2nd
    cfv
    cY
    c2nd
    cfv
    cop
    cZ
    c2nd
    cfv
    cD
    cco
    cfv
    #
    co
    #
    co
    #
    cop
    wceq
    @0
    c1st
    cfv
    @4
    wceq
    wph
    cB
    cC
    cD
    @7
    cT
    c.x
    cF
    cG
    cK
    cO
    cX
    cY
    cZ
    xpcco1st.t
    xpcco1st.b
    xpcco1st.k
    xpcco1st.1
    @7
    eqid
    xpcco1st.o
    xpcco1st.x
    xpcco1st.y
    xpcco1st.z
    xpcco1st.f
    xpcco1st.g
    xpcco
    @4
    @9
    @0
    @1
    @2
    @3
    ovex
    @5
    @6
    @8
    ovex
    op1std
    syl
end
