/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import VersoManual
import Phrasebook.Meta.Lean
import Mathlib

-- This gets access to most of the manual genre (which is also useful for textbooks)
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
-- Write a code block with ```savedLean ... ``` to save it to an external file.
open Verso.Genre.Manual.InlineLean


open Phrasebook

set_option pp.rawOnError true

#doc (Manual) "Distribution theory" =>

blubb die blubb

# Test functions

```lean -show
section TestFunction
```

- {name}`ContDiffMapSupportedIn`
- {name}`TestFunction`

```lean -show
end TestFunction
```

# Schwartz functions

```lean -show
section SchwartzMap
```

- {name}`SchwartzMap`

```lean -show
end SchwartzMap
```

# Distributions

```lean -show
section Distribution
```

- {name}`Distribution`


```lean -show
end Distribution
```

# Tempered distributions

```lean -show
section TemperedDistribution
```

- {name}`TemperedDistribution`

```lean -show
end TemperedDistribution
```
